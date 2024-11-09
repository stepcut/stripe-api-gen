{-# language CPP #-}
{-# language NoMonomorphismRestriction #-}
{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language TypeFamilies #-}
{-# language DataKinds #-}
{-# language FlexibleInstances #-}
{-# language ViewPatterns #-}
{-# language MultiWayIf #-}
module Main where

-- import Control.Monad.State (State(..), evalState)
import Control.Arrow (first)
import Control.Monad (when)
import Control.Monad.State (State, evalState)
import Data.Aeson (decode')
import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy as LBS
import Data.Char (isUpper)
import Data.Function (on)
import Data.List ((\\), partition)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.HashMap.Strict.InsOrd as InsOrd
import Data.HashMap.Strict.InsOrd (InsOrdHashMap)
import Data.Maybe (catMaybes, fromJust, isJust, isNothing, fromMaybe)
import Data.OpenApi hiding (trace)
import Data.String (IsString(fromString))
import Data.List (nub, nubBy, sortOn, sort)
import  Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Debug.Trace (trace)
import Extra
import GHC.Driver.Session (getDynFlags)
import GHC.SourceGen
import GHC.SourceGen.Name (RdrNameStr, rdrNameStrToString)
import GHC.Paths (libdir)
import GHC (runGhc, noLoc)
import GHC.Data.FastString(mkFastString)
import GHC.Data.StringBuffer (stringToStringBuffer)
import qualified GHC.Data.EnumSet  as EnumSet
import GHC.Parser
import GHC.Parser.Lexer(ParserOpts(..), P(..),ParseResult(..), PState(..), getPsErrorMessages, initParserState, mkParserOpts)
import GHC.Parser.Annotation
import qualified GHC.Hs as GHC
import GHC.Hs --  (XDocTy, NoExtField, Prefix, noExtField)
import GHC.Hs.Decls
import GHC.Hs.Doc (HsDoc, LHsDoc, WithHsDocIdentifiers(..))
import GHC.Hs.DocString
import GHC.Hs.Expr
import GHC.Hs.Type (LHsType, HsType(HsDocTy))
import GHC.Hs.Extension (GhcPs) -- Pass(Parsed), GhcPass(GhcPs))
import GHC.Types.Basic (TopLevelFlag(TopLevel), opPrec)
import GHC.Types.SrcLoc (SrcSpan, Located, GenLocated(..), mkGeneralSrcSpan, mkRealSrcLoc, unLoc)
import GHC.Types.Fixity (LexicalFixity(Prefix))
import GHC.Utils.Error (DiagOpts(..))
import GHC.Utils.Outputable (defaultSDocContext)
import Language.Haskell.TH.LanguageExtensions (Extension(DataKinds, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverlappingInstances, OverloadedStrings, RecordWildCards, StandaloneDeriving, TypeFamilies, UndecidableInstances))
import Ormolu (ormolu, defaultConfig)
import Pretty
import System.Directory (copyFile, createDirectoryIfMissing)
import System.FilePath (splitPath, takeDirectory)
import Text.Casing (pascal, camel)
import Text.PrettyPrint.GenericPretty
import Text.PrettyPrint hiding ((<>))
import Witherable (mapMaybe)

-- import Text.PrettyPrint

--import GHC.Hs.Syn
-- import GHC.Hs.Types

{-

This code generates a binding to the stripe API. It uses the stripe OpenAPI3 specification as a reference, but there are a number of fixups applied in order to generate a more palatable end result.

For example, there are many places where a field takes a 'text' value, but we want to use a newtype wrapped value for added type safety.


AnyOf is similar to OneOf.

  { _schemaTitle = Just "customer_shipping"
  , _schemaDescription = Nothing
  , _schemaRequired = ["address","name"]
  , _schemaNullable = Nothing


-- FIXUPS:

 - currency is a 3-letter string, but we can provide a ADT for it instead
 - email is a string, but we can wrap it in a newtype
 - these strings are too ambigious and need a prefix: id, type
 - expansions


-- FIXME:

  anyOf vs oneOf vs allOf. This spec doesn't use allOf, but does use anyOf vs oneOf.

For 'oneOf' the json object must match against exactly one type. If it is ambigious and possible to convert to more than one type, then things are wrong.

For 'anyOf' it means that when figuring out what the json object is -- it could be any of the listed schemas. It must validate against at least one, but doesn't have to validate against all of them. The only way to know which ones actually match a specific value is to check and see if they validate or not. anyOf could perhaps be called someOf.


-}

-- ghc-source-gen extras -- types and functions that should really be in ghc-source-gen already

type XDocTy' = XDocTy GhcPs
type LHsType' = LHsType GhcPs

multiLineDocString dec strs = MultiLineDocString dec  (NonEmpty.map (noLoc. mkHsDocStringChunk) strs)
generatedDocString str = GeneratedDocString (mkHsDocStringChunk str)

-- docVar :: (Var a) => a -> HsType'
-- docVar :: HsType GhcPs -> HsDocString -> HsType GhcPs
docVar v dstr =
 HsDocTy xt ty dc
 where
   xt :: XDocTy'
   xt = EpAnnNotUsed

   ty :: LHsType'
--   ty = noLocA v
   ty = L (SrcSpanAnn EpAnnNotUsed (mkGeneralSrcSpan "<strip-api-gen>")) v -- v -- (SrcSpanAnn EpAnnNotUsed v)

   dc :: LHsDoc pass
   dc = noLoc (WithHsDocIdentifiers dstr [])

-- We want to avoid creating duplicate definitions for the same type. So we need to track which types we have already created. It is not sufficient to merely consider the name of the type, because in the spec, sometimes the same name is used to create different types. So we also need to check that the specification for the types match.

mDocVar v Nothing = v
mDocVar v _ = v
 -- (Just txt) = docVar v (multiLineDocString HsDocStringPrevious $ NonEmpty.singleton (T.unpack txt))

-- | show a module. Addeds language extension pragmas, and formats with oromul.
showModule :: FilePath -- ^ module filepath, only used in error messages
           -> [Extension] -- ^ list of language extensions
           -> HsModule'
           -> Bool
           -> IO Text
showModule fp extensions modul o =
  do t <- runGhc (Just libdir) $
            do dflags <- getDynFlags
               pure $ showPpr dflags modul
     let pragmas = T.unlines $ map (\e -> "{-# language " <> (T.pack (show e)) <> " #-}") extensions
     if o
       then ormolu defaultConfig fp (pragmas <> T.pack t)
       else pure $ (pragmas <> T.pack t)

-- * Environment

type Env = Map Text Schema

type EnvM = State Env

-- * Read Stripe spec

readSpec :: IO OpenApi
readSpec =
  do c <- LBS.readFile "./stripe-openapi3/openapi/spec3.sdk.json"
     case decode' c of
       Nothing -> error "could not decode' spec3.sdk.json"
       (Just o) -> pure o

replace :: Char -> Char -> String -> String
replace orig new = map (\c -> if (c == orig) then new  else c)

textToPascalName :: (IsString a) => Text -> a
-- textToPascalName "ID" = fromString "ID" -- FIXME: we want all country codes to be uppercase, but we don't have enough context here
textToPascalName t = fromString . pascal . (replace '.' '_') . T.unpack $ t

textToCamelName :: (IsString a) => Text -> a
textToCamelName = fromString . camel . (replace '.' '_') . T.unpack

derivingNames = [ "Eq", "Data", "Ord", "Read", "Show"]
derivingCommon = [deriving' [ var n | n <- derivingNames ]]

typesModule :: HsModule'
typesModule =
  module' (Just "Types") Nothing []
   [ typeSig "const" $ a --> b --> a
   , funBind "const" $ match [x, wildP] x
   ]
  where
--    a' :: HsType c
--    a' = HsDocTy undefined (var "a") (noLoc (mkHsDocString "the doc for a"))
    a = docVar (var "a")  (generatedDocString "documentation for a!")
    b = var "b"
    x = bvar "x"

referencedSchemaToType :: GenStyle -> Text -> Text -> Referenced Schema -> ([(RdrNameStr, [RdrNameStr])], HsType', [HsDecl'])
referencedSchemaToType gs objName n (Inline s) = schemaToType gs objName n s
referencedSchemaToType gs objName n (Ref (Reference r)) =
  let imports
        | (objName == r) = []
        | otherwise = [(fromString $ "Component." <> textToPascalName r, [textToPascalName r]) ]
  in (imports, (var $ textToPascalName r), [])

data MkToStripeParam
  = SkipToStripeParam
  | TopToStripeParam
  | HelperToStripeParam [Text]
  deriving (Eq, Ord, Read, Show)

-- types defined in Web.Stripe.Types
webStripeTypesNames = [ "expand", "lines", "line_items", "metadata", "object", "use_stripe_sdk", "currency" ]

-- the `[HsDecl']`in the return value should probably be removed. This
-- should probably return the name of something that should already
-- exist, but it should not declare new things
schemaToType :: GenStyle
             -> Text
             -> Text
             -> Schema
             -> ([(RdrNameStr, [RdrNameStr])], HsType', [HsDecl'])
schemaToType gs objName n s =
  let (imports, ty, decls) = schemaToType' gs objName n s
  in case _schemaNullable s of
    (Just True) -> (imports, var "Maybe" @@ ty, decls)
    _           -> (imports, ty, decls)

withPrefixType :: Text -> Text -> Text
withPrefixType objNm nm =
  -- FIXME: failure_code is usually a subset of this list
  -- https://stripe.com/docs/error-codes) for a list of codes).
  -- failure_code varies from location to location

  -- in AccountCapabilities should we just use plain old Status for everything instead of generating unique status types?
  case (nm `elem` ["status", {- "setup_future_usage", "capture_method", -} "type", "mandate_options", "verification_method"]) of
    True -> (objNm <> "_" <> nm)
    _ -> nm

withPrefixEnumCon :: Text -> Text -> Text -> Text
withPrefixEnumCon objNm nm conName
  | nm `elem` [ "active_features", "allowed_categories", "blocked_categories", "funding_instructions_bank_transfer_financial_address_type", "pending_features", "restricted_features", "supported_networks", "payment_method_types" ] =
      nm <> "_" <> conName
withPrefixEnumCon objNm nm conName
  | nm `elem` [ "verification_method" ] =
      objNm <> "_" <> conName
withPrefixEnumCon objNm nm conName
  | nm `elem` [ "allowed_countries"] =
      T.toUpper conName
withPrefixEnumCon objNm nm conName =
  case conName `elem` [ "active"
                      , "always"
                      , "auto"
                      , "automatic"
                      , "credit_reversal"
                      , "debit_reversal"
                      , "if_required"
                      , "inactive"
                      , "inbound_transfer"
                      , "pending"
                      , "match"
                      , "mismatch"
                      , "not_provided"
                      , "outbound_payment"
                      , "outbound_transfer"
                      , "received_credit"
                      , "received_debit"
                      , "restricted"
                      , "stolen"
                      , "string"
                      , "unrestricted"
                      , "lost"
                      , "manual"
                      , "none"
                      , "other"
                      ] of
    True -> (nm <> "_" <> conName)
    _    -> conName

-- merge this with mkEnums
schemaToEnumDecl :: MkToStripeParam
                 -> Text    -- ^ objName -- used for disambiguation
                 -> Text    -- ^ enum name
                 -> Schema  -- ^ enum schema
                 -> (HsType', [HsDecl'], [(Text, RawValBind)])
schemaToEnumDecl instToStripeParam objName nm s
  | nm == "object" = (var "FixMeSchemaToEnumDecl", [], [])
--       (textToPascalName "stripe_object", [ data' (textToPascalName "stripe_object") [] [ prefixCon (textToPascalName ("object_" <> c)) [] | c <- Set.toList conNms ] (derivingCommon' AllDeclarations) ])

  | nm == "version" && isJust (_schemaEnum s) =
      let (Just vs) =  _schemaEnum s
          cons = [ prefixCon (textToPascalName $ "V" <> c) [] | (Aeson.String c) <- vs ]
          occName  = (textToPascalName (objName <> "_"<> nm))
          occName' = (textToPascalName (objName <> "_"<> nm))
          json = mkFromJSON objName (objName <> "_"<> nm) s
      in ((var occName ), [data' occName' [] cons derivingCommon, json], [])
  | _schemaType s == Just OpenApiString =
      case _schemaEnum s of
        (Just vs')
          | nm == "status" && ([ c | (Aeson.String c) <- vs'] ==  [ "active", "inactive", "pending" ]) ->
              (var "Status", [], [])
          | otherwise ->
              let occNam = textToPascalName $ withPrefixType objName nm
                  vs = filter (/= (Aeson.String "")) vs'
                  mkEmptyable ty = if elem (Aeson.String "") vs' then var "Emptyable" @@ ty else ty
                  -- fixme: detect if there is an "" in the list of enums and, if so, make the type Emptyable
                  matches =
                    if isEmptyable s
                    then [ match [ if (c == "") then (conP "Empty" []) else (conP "Full" [ bvar (textToPascalName $ withPrefixEnumCon objName nm c) ]) ] (string $ T.unpack (withPrefixEnumCon objName nm c)) | (Aeson.String c) <- vs' ]
                    else [ match [ bvar (textToPascalName $ withPrefixEnumCon objName nm c) ] (string $ T.unpack (withPrefixEnumCon objName nm c)) | (Aeson.String c) <- vs ]
                  inst = case instToStripeParam of
                           SkipToStripeParam -> []
                           TopToStripeParam ->
                             [ instance' ((var "ToStripeParam") @@ (mkEmptyable (var (textToPascalName $ withPrefixType objName nm))))
                                  [ funBinds "toStripeParam" [ match [ bvar "c" ]
                                                               ( var ":" @@ (tuple [string $ T.unpack $ withPrefixType objName nm,
                                                                                    case' (var "c") matches
                                                                                   ]))
                                                             ]
                                  , funBinds "toStripeParamName" [ match [ wildP ] (string $ T.unpack $ withPrefixType objName nm) ]
                                  ]
                              ]
                           _ -> []
                  toStripeParamBuilder =
                    case instToStripeParam of
                      HelperToStripeParam path ->
                        let funName = T.concat (path ++ [nm])
                            matches = [ match [ bvar (textToPascalName $ withPrefixEnumCon objName nm c) ]
                                        (list [ tuple [ string $ T.unpack $ mkKey (path ++ [nm])
                                                      , string $ T.unpack (withPrefixEnumCon objName nm c)
                                                      ]
                                              ])
                                      | (Aeson.String c) <- vs ]
                        in [( funName
                            , funBind (fromString $ T.unpack funName)
                               (if isEmptyable s
                                 then (match [ bvar "mc" ]
                                       (case' (var "mc")
                                            [ match [ conP "Empty" [] ] (list [ tuple [ string $ T.unpack $ mkKey (path ++ [nm]), string "" ] ] )
                                            , match [ conP "Full" [ bvar "c" ] ] (case' (var "c") matches)
                                            ]))
                                 else (match [ bvar "c" ] (case' (var "c") matches))
                               )
                            )]
                      _ -> []

                  cons   = [ prefixCon (textToPascalName $ withPrefixEnumCon objName nm c) [] | (Aeson.String c) <- vs ]
                  json = mkFromJSON objName nm s
              in (mkEmptyable (var (fromString occNam)), (data' (fromString occNam) [] cons derivingCommon) : json : inst, toStripeParamBuilder)
        Nothing ->
          let typName = textToPascalName nm
              cons     = [ recordCon (fromString $ textToPascalName nm) [ ((fromString $ "un" <> textToPascalName nm)
                                                                          , (strict $ field $ var (fromString "Text"))
                                                                          )
                                                                        ]
                         ]
              inst = case instToStripeParam of
                       SkipToStripeParam -> []
                       TopToStripeParam -> [ instance' ((var "ToStripeParam") @@ (var (textToPascalName nm)))
                                  [ funBinds "toStripeParam" [ match [ conP (fromString (textToPascalName nm)) [ bvar "t" ] ]
                                                               ( var ":" @@ (tuple [string $ T.unpack nm
                                                                                   , var "encodeUtf8" @@ var "t"
                                                                                   ]) )
                                                             ] ]
                               ]
                       _ -> []
                       {-
              toStripeParamBuilder =
                    case instToStripeParam of
                      HelperToStripeParam path ->
                        let funName = T.concat (path ++ [nm])
{-
                            matches = [ match [ bvar (textToPascalName $ withPrefixEnumCon objNm nm c) ] (list [ tuple [ string $ T.unpack $ mkKey (path ++ [nm])
                                                                                                          , string $ T.unpack (withPrefixEnumCon objNm nm c)
                                                                                                          ] ])
                                      ]
-}
                        in [( funName
                            , funBind (fromString $ T.unpack funName)
--                               (match [conP (fromString (textToPascalName $ tyName)) [ bvar "n" ]] (var "id")))
--                               (match [ bvar "c" ] (case' (var "c") matches))
                               (match [ bvar "c" ] (var "error" @@ string "not implemented"))  -- (case' (var "c") matches))
                            )
                           ]
                      _ -> []
               -}
          in (var (fromString typName) , (data' (fromString typName) [] cons derivingCommon) : inst, [])

{-

Handling OpenApiObject

https://swagger.io/docs/specification/data-models/data-types/#object

There are a few types of objects.

If only the properties is set, then we have a list of field names and field types.

if only the additional properties is set and as 'type' value set, then we have a bunch of key value pairs where the key is a text.

It is also possible to have a freeform object:

type: object
additionalProperties: true

This is equivalent to:

type: object
additionalProperties: {}

In this case the dictionary values can be any type.

It is not clear if you can mix properties and additionalProperties.

-}

-- | list type things with data, has_more, url
isList :: Schema -> Bool
isList s =
  let props = _schemaProperties s
  in and [ InsOrd.member "data" props
         , InsOrd.member "has_more" props
         , InsOrd.member "object" props
         , InsOrd.member "url" props
         ]

isRangeQuerySpec :: Schema -> Bool
isRangeQuerySpec s =
  case _schemaTitle s of
    (Just t) | t == "range_query_specs" -> True
    _ -> False

isAnyOfRangeQuerySpec :: Schema -> Bool
isAnyOfRangeQuerySpec s =
  case _schemaAnyOf s of
    (Just [(Inline schema1), (Inline schema2)]) -> isRangeQuerySpec schema1 && (_schemaType schema2 == Just OpenApiInteger)
    _ -> False

schemaToType' :: GenStyle
              -> Text
              -> Text
              -> Schema
              -> ([(RdrNameStr, [RdrNameStr])], HsType', [HsDecl']) -- ^
schemaToType' gs p n s
--  | n == "type" = ([], var "StripeType", [])
   -- types imported from Web.Stripe.Types
--  | n `elem` webStripeTypesNames = ([], var $ textToPascalName n, [])
  | ((n == "type") && (_schemaType s == Just OpenApiString)) && (_schemaEnum s == Nothing)  = ([], var "Text", [])
  | n == "type" =  ([], var $ textToPascalName (p <> "_type"), [])
  | n == "status"  && (_schemaEnum s == Nothing) && (_schemaType s == Just OpenApiString) =  ([], var "Text", [])
  | n == "status"  && ([ c | (Aeson.String c) <- (fromJust $ _schemaEnum s)] ==  [ "active", "inactive", "pending" ]) =  ([], var $ textToPascalName "status", [])
  | n == "status" =  ([], var $ textToPascalName (p <> "_status"), [])
  | n == "version" && isJust (_schemaEnum s) = ([],  var $ textToPascalName (p <> "_version"), [])

  | (_schemaType s == Just OpenApiInteger) && (_schemaFormat s == Just "unix-time") =
--      ([], var "UTCTime", [])
      ([], var "Integer", [])

  | (_schemaType s == Just OpenApiInteger) =
      case _schemaFormat s of
        (Just "int32") -> ([], var "Int32", [])
        (Just "int64") -> ([], var "Int64", [])
        _              -> ([], var "Integer", [])
  | (_schemaType s == Just OpenApiBoolean) =
      ([], var "Bool", [])
  | (_schemaType s == Just OpenApiNumber) =
      case _schemaFormat s of
        (Just "float")  -> ([], var "Float", [])
        (Just "double") -> ([], var "Double", [])
        _               -> ([], var "Double", [])
  | (_schemaType s == Just OpenApiString) =
    case n of
      "currency" -> ([], var "Currency", [])
      "object"   -> ([], var "Text", [])
      _ -> case _schemaEnum s of
             Nothing -> ([], var "Text", [])
{-
             Just [ Aeson.String "active"
                  , Aeson.String "inactive"
                  , Aeson.String "pending"
                  ]
               -> ([], var $ "Status", []) -- schemaToEnumDecl p n s
-}
             (Just enums) ->
               ([], (var $ textToPascalName (withPrefixType p n)), [] {- mkEnums gs n (Map.singleton n (Set.fromList [ s | Aeson.String s <- enums ] ))-} )
{-
               [ data' (textToPascalName typeNm) [] [ mkCon typeNm c | c <- Set.toList conNms ] derivingCommon
               , instance' (var "FromJSON" @@ (var $ textToPascalName typeNm)) [ funBinds "parseJSON" [ match []  (var "undefined")] ]
               ]
-}
             _       -> ([], var $ textToPascalName n, []) -- schemaToEnumDecl p n s
  | (_schemaType s == Just OpenApiArray) =
      case _schemaItems s of
        Just (OpenApiItemsObject (Ref (Reference r))) ->
          ([(fromString $ "Component." <> textToPascalName r, [textToPascalName r])], {- var "StripeList" -} listTy (var $ textToPascalName r), [])
        Just (OpenApiItemsObject (Inline s)) ->
              let name = {- case _schemaTitle s of
                    (Just t) -> t
                    Nothing  -> -} n
                  (imports, ty, decls) = schemaToType' gs "FixMe4a" name s
              in (imports, {- var "StripeList" @@ -} listTy ty, decls)
        Nothing -> ([], var "FixMeOpenApiItemsObject", [])
  | (_schemaType s == Just OpenApiObject) =
      case (_schemaAdditionalProperties s) of
        (Just (AdditionalPropertiesSchema rSchema)) ->
          let (imports, ty, decls) = referencedSchemaToType gs p n rSchema
          in (imports, var (fromString "Map") @@ var (fromString "Text") @@ ty, decls)
        _ ->
          case isList s of
            -- handle things which can be expressed via the 'Lines a' type
            True ->
              case InsOrd.lookup "data" (_schemaProperties s) of
                (Just (Inline dataSchema)) ->
                  case _schemaItems dataSchema of
                    (Just (OpenApiItemsObject r)) ->
                      let (imports, ty, decls) = referencedSchemaToType gs p "FixMeLines" r
                      in (imports, var (fromString "Lines") @@ ty, decls)
                    Nothing -> error "Expected 'lines.data' to have an 'items' property"
                Nothing -> error "Expected 'lines' to have a data property"

            False ->
              let (imports, decls, toStripeParamBuilder) = schemaToTypeDecls gs False SkipToStripeParam p n s
                  nm = {-
                    case InsOrd.lookup "resourceId" (_unDefs $ _schemaExtensions s) of
                      (Just (Aeson.String t)) -> t
                      Nothing ->
                        case _schemaTitle s of
                          (Just t) -> t
                          Nothing  -> -} n
{- case _schemaTitle s of
                    (Just t) -> t
                    Nothing  ->  n -}
              in (imports, var (fromString $ textToPascalName (withPrefixType p nm)), decls)
    -- FIXME: for things that are parameters, instead of OneOf couldn't we just use multiple StripeHasParam instances
  | isJust (_schemaAnyOf s) =
      case _schemaAnyOf s of
        (Just [(Inline schema1), (Ref (Reference r))])
          | (_schemaType schema1) == Just OpenApiString ->
              let r' | False {- r `elem` [ "balance_transaction_source", "payment_source" ] -} = r
                     | otherwise = r <> "_id"
              in (if p == r then [] else [(fromString $ "Component." <> textToPascalName r, [textToPascalName r'])], var "Expandable" @@ (var $ fromString $ textToPascalName r'), [])
        _ ->
          case InsOrd.lookup "expansionResources" (_unDefs $ _schemaExtensions s) of
            -- we are dealing with an expandable field
            (Just er)
              | n == "discounts" -> -- FIXME: this could also expand to deleted_discount
                  ([ (fromString $ "Component." <> textToPascalName "discount", [textToPascalName ("discount_id")])
                   , (fromString $ "Component." <> textToPascalName "deleted_discount", [textToPascalName ("deleted_discount_id")])
                   ], var "Expandable" @@ (var "OneOf" @@ (listPromotedTy [ var $ fromString $ textToPascalName ("discount_id")
                                                                          , var $ fromString $ textToPascalName ("deleted_discount_id")
                                                                          ])), [])
              | n == "account_tax_ids" -> -- FIXME: this could also expand to deleted_account_tax_id
                  ([ (fromString $ "Component." <> textToPascalName "tax_id", [textToPascalName ("tax_id_id")])
                   , (fromString $ "Component." <> textToPascalName "deleted_tax_id", [textToPascalName ("deleted_tax_id_id")])
                   ], var "Expandable" @@ (var "OneOf" @@ (listPromotedTy [ var $ fromString $ textToPascalName ("tax_id_id")
                                                                          , var $ fromString $ textToPascalName ("deleted_tax_id_id")
                                                                          ])), [])

              | not (n `elem` ["default_source", "destination"]) -> -- FIXME: the problem here is that the ID can expand to one of several fields
              ([(fromString $ "Component." <> textToPascalName n, [textToPascalName (n <> "_id")])], var "Expandable" @@ (var $ fromString $ textToPascalName (n <> "_id")), [])
            _ ->
              case _schemaAnyOf s of
                (Just [Inline schema1, Inline schema2])
                  | (_schemaType schema1 == Just OpenApiObject) && (_schemaEnum schema2 == Just [ Aeson.String "" ]) ->
                      let (imports, ty, decls) = schemaToType' gs p n schema1
                      in (imports, var "Emptyable" @@ ty, decls)
                (Just [Inline schema1, Inline schema2])
                  | (_schemaType schema1 == Just OpenApiArray) && (_schemaEnum schema2 == Just [ Aeson.String "" ]) ->
                      let (imports, ty, decls) = schemaToType' gs p n schema1
                      in (imports, var "Emptyable" @@ ty, decls)
                (Just [Inline schema1, Inline schema2])
                  | (_schemaType schema1 == Just OpenApiString) && (_schemaEnum schema2 == Just [ Aeson.String "" ]) ->
                      ([], var "Emptyable" @@ var "Text", [])
                (Just [Ref (Reference r)]) ->
                  ([(fromString $ "Component." <> textToPascalName r, [textToPascalName r])], (var $ fromString $ textToPascalName r), [])
                o ->
                  let (Just schemas) = _schemaAnyOf s
                      (imports, types, decls) = unzip3 $ map (referencedSchemaToType gs p "FixMe7") schemas
                  in (concat imports, var "OneOf" @@ listPromotedTy types, concat decls)

schemaToType' _ p n s = error $ show $ (n, ppSchema s)
-- schemaToType' _ _ = (var "FixMe", [])
{-
mkNullable :: Schema -> HsType' -> HsType'
mkNullable s ty =
  case _schemaNullable s of
    (Just True) -> var "Maybe" @@ ty
    _           -> ty
-}
textToOccName = fromString . T.unpack

mkRequired :: (Var a, App a) => Bool -> a -> a
mkRequired True a = a
mkRequired False a = var "Maybe" @@ a

-- when do we use _schemaNullable and when do we use _schemaRequired?
schemaToField :: GenStyle -> Bool -> MkToStripeParam -> [ParamName] -> Text -> (Text, Referenced Schema) -> ([(RdrNameStr, [RdrNameStr])], (OccNameStr, Field), [HsDecl'], [(Text, RawValBind)])
schemaToField gs wrapPrim instStripeParam required objectName (n, Inline s)
  | n == "object" && (_schemaType s == Just OpenApiString) =
    let toStripeBuilder = case instStripeParam of
                      HelperToStripeParam path ->
                        let funName = T.concat (path ++ [n])
--                        in [(funName, valBind (fromString $ T.unpack funName) (var "id"))]
                        in [( funName
                            , funBind (fromString $ T.unpack funName)
--                               (match [conP (fromString (textToPascalName $ tyName)) [ bvar "n" ]] (var "id")))
                               (match [ bvar "n" ] (list [(tuple [string $ T.unpack $ mkKey (path ++ [n]), var "encodeUtf8" @@ var "n"])]))
                            )
                           ]
                      _ -> []
    in
      ([]
      , (fromString $ textToCamelName (objectName <> "_" <> n), strict $ field $ mkRequired (n `elem` required) $ var "Text")
      , []
      , toStripeBuilder
      )
      -- sometimes the 'object' field is just a String, but sometimes it is actually an object.
  | n == "object" && (_schemaType s == Just OpenApiObject) =
      ([]
      , (fromString $ textToCamelName (objectName <> "_" <> n), strict $ field $ mkRequired (n `elem` required) $ var "Object")
      , []
      , []
      )
schemaToField gs wrapPrim instStripeParam required objectName (n, Inline s)
  | n == "id" && _schemaType s == Just OpenApiString =
      -- we don't need to import this id because it is an id that is defined in the local module. Importing it would just cause the module to import itself.
      ([{- (textToPascalName objectName , [textToPascalName $ objectName <> "_id"])-}]
      , (fromString $ textToCamelName (objectName <> "_" <> n), strict $ field $ mkRequired (n `elem` required) $ var (fromString $ textToPascalName (objectName <> "_id")))
      , mkId gs objectName
      , []
      )
{-
  | _schemaType s == Just OpenApiInteger && (n `elem` ["amount", "amount_captured", "amount_refunded", "application_fee_amount"]) =
      let ty = if ((Just True == _schemaNullable s) || ((not $ null required)  && (not $ n `elem` required)))
               then var "Maybe" @@ var "Amount"
               else var "Amount"
      in ([]
         , (fromString $ textToCamelName (objectName <> "_" <> n), strict $ field $ ty)
         , []
         , []
         )
-}
-- schemaToField _ (n , Ref _)   = ((textToOccName n, strict $ field $ var "FixMe3"), [])
schemaToField gs wrapPrim instStripeParam required objectName (n , Ref (Reference r))   =
  ( [(fromString $ "Component." <> textToPascalName r, [textToPascalName r])]
  , (fromString $ textToCamelName (objectName <> "_" <> n), strict $ field $ mkRequired (n `elem` required) $ var $ textToPascalName r )
  , []
  , []
  )
schemaToField gs wrapPrim instStripeParam required objectName (n, Inline s)
  | n == "up_to" && isUpToInf s =
    let toStripeBuilder = case instStripeParam of
                      HelperToStripeParam path ->
                        let funName = T.concat (path ++ [n])
--                        in [(funName, valBind (fromString $ T.unpack funName) (var "id"))]
                        in [( funName
                            , funBind (fromString $ T.unpack funName)
--                               (match [conP (fromString (textToPascalName $ tyName)) [ bvar "n" ]] (var "id")))
                               (match [ bvar "n" ] (list [(tuple [string $ T.unpack $ mkKey (path ++ [n]), var "toBytestring" @@ var "n"])]))
                            )
                           ]
                      _ -> []

    in
       ( []
       , (fromString $ textToCamelName n, strict $ field $ var "UpTo")
       , []
       , toStripeBuilder
       )
schemaToField gs wrapPrim instStripeParam required objectName (n, Inline s) =
   let (imports, ty, _decls) = schemaToType gs objectName n s
       (imports', decls, toStripeParamBuilder) = schemaToTypeDecls gs wrapPrim instStripeParam objectName n s
   in -- if (objectName == "tiers" && n == "flat_amount") then error (show $ (map fst toStripeParamBuilder, wrapPrim, objectName, n, ppSchema s)) else
     ( imports ++ imports'
      , ( fromString $ textToCamelName (objectName <> "_" <> n)
        , strict $ field $ mkRequired (n `elem` required) $ ty
        )
      , decls
      , if (n `elem` required)
        then toStripeParamBuilder
        else map mkMaybeParam toStripeParamBuilder
      )

mkMaybeParam :: (Text, RawValBind) -> (Text, RawValBind)
mkMaybeParam (n,f) =
  ("m" <> n, funBind (fromString $ T.unpack ("m" <> n))
             (match [ bvar "mv"] (case' (var "mv")
                                   [ match [ conP "Nothing" [] ] (list [])
                                   , match [ conP "Just" [ bvar "v" ] ]
                                     (let' [f] ((var $ fromString $ T.unpack n) @@ (var "v")))
                                   ]
                                 )
             ))

{-
schemaToField gs required objectName (n, Inline s)
  | (isJust $ _schemaEnum s) && objectName == "mandate" = error $ show (n, s)
-}
-- schemaToField gs required objectName (n, Inline s)
--  | n == "discounts" = error $ show (n, s)


{- check for stuff like this,

     "on_behalf_of": {
       "anyOf": [
         {
           "type": "string"
         },
         {
           "enum": [
             ""
           ],
           "type": "string"
         }
       ],
       "description": "The account on behalf of which to charge, for each of the subscription's invoices."
     },

-}
isEmptyableString :: Schema -> Bool
isEmptyableString s =
  case _schemaAnyOf s of
    (Just [Inline schema1, Inline schema2]) ->
      (_schemaType schema1 == Just OpenApiString) && (_schemaEnum schema2 == Just [ Aeson.String "" ])
    _ -> False


isEmptyable :: Schema -> Bool
isEmptyable s =
  case _schemaAnyOf s of
    (Just [Inline schema1, Inline schema2]) ->
      (_schemaEnum schema2 == Just [ Aeson.String "" ])
    _ -> case (_schemaEnum s) of
           (Just vs) -> elem (Aeson.String "") vs
           _ -> False

isEmptyEnum :: Schema -> Bool
isEmptyEnum schema =
  (_schemaEnum schema == Just [ Aeson.String "" ])

isUpToInf :: Schema -> Bool
isUpToInf s =
  case _schemaAnyOf s of
    (Just [(Inline schema1), (Inline schema2)]) ->
      (_schemaType schema2 == Just OpenApiInteger) &&
      (case _schemaEnum schema1 of
         (Just [ Aeson.String s ]) -> s == "inf"
         _ -> False)
    _ -> False

mkNewtypeParam tyName wrappedType =
  let occName   = fromString (textToPascalName tyName)
      conName   = fromString (textToPascalName tyName)
      unConName = fromString ("un" <> textToPascalName tyName)
      con       = recordCon occName [ ( unConName, field $ wrappedType) ]
  in ([], [ newtype' occName [] con derivingCommon ])


-- FIXME: we have to add a unique prefix to each sum type. But that just seems to make things more annoying for the user? Maybe we should just use OneOf? The user of this library is passing the values in, not trying to figure out which instance it actually is?
mkSumType :: Text -> [Referenced Schema] -> [HsDecl']
mkSumType tyName schemas =
  let occName   = fromString (textToPascalName tyName)
      (cons, decls) = unzip $ map mkCon schemas
--      conName   = fromString (textToPascalName tyName)
--      unConName = fromString ("un" <> textToPascalName tyName)
--      con       = recordCon occName [ ( unConName, strict $ field $ wrappedType) ]
  in (data' occName [] cons derivingCommon) : concat decls
  where
    mkCon (Ref (Reference r)) =
      let conName = fromString (prefix <> textToPascalName r)
          fld     = strict $ field $ var $ fromString (prefix <> textToPascalName r)
      in (prefixCon conName [fld], [])
    prefix = filter isUpper (textToPascalName tyName)
--  error $ (T.unpack $ "tyName = " <> tyName <> " , schemas = ") <> show schemas

data GenStyle
  = AllDeclarations
  | HsBoot
  deriving (Eq, Ord, Read, Show)

derivingCommon' AllDeclarations = derivingCommon
derivingCommon' HsBoot          = []

{-
We generating an Object -- we probably do not need to wrap ever Text and Bool in a newtype. But we do need to wrap those values when they are being used as parameters to a request. This code does not currently distinguish those situations"
-}

mkKey :: [Text] -> Text
mkKey [] = ""
mkKey (p:ps) =
  p <> mkSquare ps
  where
    mkSquare :: [Text] -> Text
    mkSquare [] = ""
    mkSquare (k:ks) = "[" <> k <> "]" <> mkSquare ks


referencedSchemaToTypeDecls :: GenStyle -> Bool -> MkToStripeParam -> Text -> Text -> Referenced Schema -> ([(RdrNameStr, [RdrNameStr])], [HsDecl'], [(Text, RawValBind)])
referencedSchemaToTypeDecls gs wrapPrim instToStripeParam objName tyName (Inline s) = schemaToTypeDecls gs wrapPrim instToStripeParam objName tyName s
referencedSchemaToTypeDecls gs wrapPrim instToStripeParam objName tyName  (Ref (Reference r)) =
  trace ("referencedSchemaToTypeDecls - should we do something here? " ++ show r) ([],[],[])
  {-
  let imports
        | (objName == r) = []
        | otherwise = [(textToPascalName r, [textToPascalName r]) ]
  in (imports, (var $ textToPascalName r), [])
-}

{-
FIXME: wrapPrim is used because stripe params need to have unique type names. So values that will be used as params need wrappers.
However this code seems to only provide stripeParamBuilders for wrapped values -- which is probably not right. When we have a record with a bunch of fields, schemaToField needs builders for each field, but the fields that have primitive values don't need to be wrapped. Though perhaps schemaToField can just ignore the newtypes if it does not need them?
-}
schemaToTypeDecls :: GenStyle -> Bool -> MkToStripeParam -> Text -> Text -> Schema
                  -> ([(RdrNameStr, [RdrNameStr])], [HsDecl'], [(Text, RawValBind)])
schemaToTypeDecls gs wrapPrim instToStripeParam objName tyName s
  -- types which are manually defined in Types
  | tyName `elem` webStripeTypesNames =
      let toStripeParamBuilder =
            case instToStripeParam of
              HelperToStripeParam path ->
                let funName = T.concat (path ++ [tyName])
                in [( funName
                    , funBind (fromString $ T.unpack funName)
                       (match [ bvar "t" ] (list [(tuple [ string $ T.unpack $ mkKey (path ++ [tyName])
                                                         , var "error" @@ string "add support for metadata in toStripeParam"
                                                         ])
                                                 ]))
                    )]
            in ([],[], toStripeParamBuilder)
  {-
  | tyName `elem` [ {- "Created", "Limit" , "EndingBefore", "StartingAfter" -} ] = ([], [], [])
  | tyName `elem` [ "object" ] = ([],[],[])
  | tyName `elem` [ "expand", "metadata"] = ([], [], [])
  | tyName `elem` ["lines", "line_items", "use_stripe_sdk", {- "refunds",-} {- "customer_id", -} {- "automatic_tax", -} "currency"] = ([], [], [])
-}
  | isList s = ([], [], [])
  {-
  | tyName == "default_tax_rates" =
      -- FIXME: The docs says  'Pass an empty string to remove previously-defined tax rates'. Does passing an empty list do that?
      case _schemaAnyOf s of
        (Just [Inline schema1, Inline schema2])
          | _schemaEnum schema2 == Just [ Aeson.String "" ] &&
            _schemaType schema1 == Just OpenApiArray ->
              case _schemaItems schema1 of
                (Just (OpenApiItemsObject (Inline itemSchema)))
                  | (_schemaType itemSchema == Just OpenApiString) ->
                    let occName   = fromString (textToPascalName tyName)
                        conName   = fromString (textToPascalName tyName)
                        unConName = fromString ("un" <> textToPascalName tyName)
                        con       = recordCon occName [ ( unConName, strict $ field $ listTy $ var "TaxRateId") ]
                    in ([], [ newtype' occName [] con (derivingCommon' gs) ])

                _ -> error "could not default_tax_rates: was expecting an array of strings but something does not match."
        _  -> error "default_tax_rates specification does not match expectations. The spec must have been updated."
  | tyName == "on_behalf_of" =
      case isEmptyableString s of
        False -> error $ "expected on_behalf_of to be a Maybe String. Perhaps the specification has changed?\n" ++ show (ppSchema s)
        True -> mkNewtypeParam tyName (var "Emptyable" @@ var "AccountId")
  | tyName == "default_tax_rate" =
      case isEmptyableString s of
        False -> error "expected default_tax_rate to be a Maybe String. Perhaps the specification has changed?"
        True -> mkNewtypeParam tyName (var "Emptyable" @@ var "AccountId")
-}
    -- just a plain old text field -- no enumeration
--  | _schemaType s == Just OpenApiString && (isNothing $ _schemaEnum s) && (tyName == "id") = ([],mkId gs objName,[])
  | _schemaType s == Just OpenApiString && (isNothing $ _schemaEnum s) =
      let toStripeParamBuilder =
                    case instToStripeParam of
                      HelperToStripeParam path ->
                        let funName = T.concat (path ++ [tyName])
                        in [( funName
                            , funBind (fromString $ T.unpack funName)
                               (match [ bvar "txt" ] (list [(tuple [string $ T.unpack $ mkKey (path ++ [tyName]), var "encodeUtf8" @@ var "txt" ])]))
                            )
                           ]
                      TopToStripeParam  -> []
                      SkipToStripeParam -> []

      in if wrapPrim -- FIXME actually wrap the prim?
         then let occName = fromString (textToPascalName $ tyName)
                  con = recordCon occName [ (textToCamelName $ "un_" <> tyName, field $ var "Text" ) ]
                  inst = case instToStripeParam of
                        SkipToStripeParam -> []
                        TopToStripeParam ->
                          [ instance' ((var "ToStripeParam") @@ (var (textToPascalName tyName)))
                                  [ funBinds "toStripeParam" [ match [ conP (fromString (textToPascalName $ tyName)) [ bvar "txt" ] ]
                                                               ( var ":" @@ (tuple [string $ T.unpack tyName, var "encodeUtf8" @@ var "txt"
                                                                                   ]) )
                                                             ]
                                  , funBinds "toStripeParamName" [ match [ wildP ] (string $ T.unpack tyName) ]
                                  ]
                          ]
                        _ -> []
              in ([], newtype' occName [] con (derivingCommon' gs) : inst, toStripeParamBuilder)
         else ([],[], toStripeParamBuilder)
  | _schemaType s == Just OpenApiString =
      let (_, d, b) = schemaToEnumDecl instToStripeParam objName tyName s
      in ([], d, b)
      -- ([], []) --

  | isJust (_schemaAnyOf s) =
      case _schemaAnyOf s of
{-
        -- this is probably the case where the value is 'expandable'.
        -- The spec should have 'x-expansionResources', but the current
        -- version of the openapi3 library does not expose that value.
        (Just [(Inline schema1), (Ref (Reference r))])
          | (_schemaType schema1) == Just OpenApiString ->
              []
-}
        -- check for NowOrLater
        (Just [(Inline schema1), (Inline schema2)])
          |  _schemaEnum   schema1 == Just [ Aeson.String "now" ] &&
            (_schemaType   schema2 == Just OpenApiInteger) &&
            (_schemaFormat schema2 == Just "unix-time")
            -> let occName   = fromString (textToPascalName tyName)
                   conName   = fromString (textToPascalName tyName)
                   unConName = fromString ("un" <> textToPascalName tyName)
                   con       = recordCon occName [ ( unConName, field $ var "NowOrLater") ]
                   inst      = case instToStripeParam of
                                 SkipToStripeParam -> []
                                 TopToStripeParam ->
                                   [instance' ((var "ToStripeParam") @@ (var (textToPascalName tyName)))
                                        [ funBinds "toStripeParam"
                                          [ match [ conP (textToPascalName tyName) [ conP "Now" []] ]
                                            ( var ":" @@ (tuple [ string $ T.unpack tyName
                                                                , string "now"
                                                                ]) )
                                          , match [ conP (textToPascalName tyName) [ conP "Later" [ bvar "utc" ] ] ]
                                            ( var ":" @@ (tuple [ string $ T.unpack tyName
                                                                , var "toBytestring" @@ (var "toSeconds" @@ var "utc")
                                                                ]) )
                                          ]
                                        , funBinds "toStripeParamName" [ match [ wildP ] (string $ T.unpack tyName) ]
                                        ]
                                       ]
               in ([], (newtype' occName [] con (derivingCommon' gs) : inst), [])
        _ ->
          case InsOrd.lookup "expansionResources" (_unDefs $ _schemaExtensions s) of
            Nothing ->
              case _schemaAnyOf s of
                (Just [Inline schema1, Inline schema2])
                  | isEmptyEnum schema2 ->
                    let (imports, decls, builders) = schemaToTypeDecls gs wrapPrim instToStripeParam "NoObjectName" tyName schema1
                    in case builders of
                         [] -> (imports, decls, []) -- should this ever be []? Or does this mean we have not handled all the cases yet? 
                         [(n, b)] ->
                           case instToStripeParam of
                             (HelperToStripeParam path) ->
                               let funNameE = n <> "_emptyable"
                                   emptyBuilder =
                                           funBinds (fromString $ T.unpack funNameE)
                                            [ match [ conP "Empty" []] (list [ tuple [ string $ T.unpack $ mkKey (path ++ [tyName]), string "" ] ] )
                                            , match [ conP "Full" [ bvar "ec" ] ]
                                              ( let' [b] (var (fromString $ T.unpack n) @@ var "ec"))
                                            ]

                               in (imports, decls, [(funNameE, emptyBuilder)])
                             _ -> (imports, decls, [(n,b)]) -- [] -- error $ show (map fst builders)
                -- if the AnyOf only contains a single item, why bother wrapping it up?
                (Just [Ref schema1]) ->
                  ([],[],[])
                (Just schemas) ->
--                  mkSumType tyName schemas --
                  let mkName :: Referenced Schema -> Text
                      mkName (Ref _)  = "FixMe6a"
                      mkName (Inline s) =
                        case _schemaTitle s of
                          Nothing  -> "FixMe6b"
                          (Just t) -> t
                      (imports, types, decls) = unzip3 $ map (\s -> referencedSchemaToType gs objName (mkName s) s) schemas
                      (imports', decls', toStripeParamBuilder') = unzip3 $ map (referencedSchemaToTypeDecls gs wrapPrim instToStripeParam "FixMe6c" tyName) schemas
                      occName   = fromString (textToPascalName tyName)
                      conName   = fromString (textToPascalName tyName)
                      unConName = fromString ("un" <> textToPascalName tyName)
                      cons = [ recordCon conName [ (unConName, strict $ field $ (var "OneOf" @@ listPromotedTy types)) ]
                             ]
                      instances =
                        if (tyName `elem` ["balance_transaction_source", "payment_source"])
                               then (if gs == AllDeclarations
                                      then [standaloneDeriving (var n @@ (var "Expandable" @@ (var $ textToPascalName (tyName <> "_id")))) | n <- derivingNames ]
                                      else [instance' (var n @@ (var "Expandable" @@ (var $ textToPascalName (tyName <> "_id")))) [] | n <- derivingNames ]
                                    )
--                               then [standaloneDeriving (var n @@ (var "Expandable" @@ (var $ textToPascalName tyName))) | n <- derivingNames ]
                               else []
                      (typeImports, typeDecls) =
                        let refId (Ref (Reference r)) = Just $ (( fromString $ "Component." <> (textToPascalName r), [ textToPascalName (r <> "_id") ]), (var $ textToPascalName (r <> "_id")))
                            refId (Inline s') = Nothing -- error (show s)
                            (typeImports', refIds) = unzip $ catMaybes $ map refId schemas
                            fakeType (Ref (Reference r)) =
                              Just (newtype' (textToPascalName $ r <> "_id") [] (prefixCon (textToPascalName $ r <> "_id") [ field $ var "String" ]) [])
                            fakeType _ = Nothing
                            fakeTypes = if gs == AllDeclarations
                                        then []
                                        else [] -- catMaybes (map fakeType schemas)
                        in (typeImports', [ data' (textToPascalName $ tyName <> "_id") [] -- it would be nicer if this was type alias, but I can't make the .hs-boot files play nicely
                                              (if gs == AllDeclarations
                                               then [ recordCon (textToPascalName $ tyName <> "_id")
                                                      [ ( (fromString $ "un" <> (textToPascalName $ tyName <> "_id") )
                                                        , (strict $ field $ var "OneOf" @@ listPromotedTy refIds)
                                                        )
                                                      ]
                                                    ]
                                               else [])
                                              (if gs == AllDeclarations
                                               then [ deriving' [ var "Read"
                                                                , var "Show"
                                                                , var "Eq"
                                                                , var "Ord"
                                                                , var "Data"
                                                                , var "Typeable"
                                                                ]
                                                    ]
                                               else [
                                                    ]
                                              )
                                          , if gs == AllDeclarations
                                            then instance' (var "FromJSON" @@ var (textToPascalName $ tyName <> "_id"))
                                                    [ funBinds "parseJSON" [ match [ bvar "v" ]
                                                                               (op' (var $ textToPascalName $ tyName <> "_id") "<$>" (var "parseJSON" @@ var "v"))
                                                                           ]
                                                    ]
                                            else instance' (var "FromJSON" @@ var (textToPascalName $ tyName <> "_id")) []
                                          ])
                      toStripeParam = case instToStripeParam of
                                             SkipToStripeParam -> []
                                             TopToStripeParam ->
                                               [ instance' ((var "ToStripeParam") @@ (var (textToPascalName tyName)))
                                                  []
                                               ]
                                             (HelperToStripeParam path) ->
                                               [
                                               ]


                      dataDecls =
                        if gs == AllDeclarations
                        then  data' occName [] cons derivingCommon : mkFromJSON objName tyName s :
                              typeInstance' ("ExpandsTo "<> T.unpack (textToPascalName (tyName <> "_id"))) hsOuterImplicit [] Prefix (var $ fromString $ T.unpack $ textToPascalName tyName) :
                              toStripeParam ++ instances
                              -- the are things that are anyOf things which are ids. We should probably detect this pattern, but it is rare enough that this list works for now.
                        else  data' occName [] [] [] :
                              ( instance' (var "FromJSON" @@ var (textToPascalName tyName)) []) :
                              [ instance' (var n @@ var (textToPascalName tyName)) [] | n <- derivingNames ] ++  instances
                  in (typeImports ++ concat (imports ++ imports'), typeDecls ++ dataDecls ++ (concat decls), concat toStripeParamBuilder')

{-
            Nothing ->
              let (Just schemas) = _schemaAnyOf s
                  (imports, types, decls) = unzip3 $ map (referencedSchemaToType objName "FixMe6") schemas
--          decls = [] -- map schemaToTypeDecls
                  occName   = fromString (textToPascalName tyName)
                  conName   = fromString (textToPascalName tyName)
                  unConName = fromString ("un" <> textToPascalName tyName)
                  cons = [ recordCon conName [ (unConName, strict $ field $ (var "OneOf" @@ listPromotedTy types)) ]
                         ]
              in (data' occName [] cons derivingCommon : mkFromJSON objNm objName s : [] {- :  concat decls -} )
-}
            (Just er) ->
              ([], [], [])
            --  error $ show er

  | (_schemaType s == Just OpenApiInteger) =
      let toStripeParamBuilder =
                    case instToStripeParam of
                      HelperToStripeParam path ->
                        let funName = T.concat (path ++ [tyName])
                        in [( funName
                            , funBind (fromString $ T.unpack funName)
                               (match [ bvar "n" ] (list [(tuple [string $ T.unpack $ mkKey (path ++ [tyName]), var "toBytestring" @@ var "n"])]))
                            )
                           ]
                      _ -> []
      in
       if wrapPrim
       then let occName = fromString (textToPascalName $ tyName)
                con = recordCon occName [ (textToCamelName $ "un_" <> tyName, field $ var "Integer" ) ]
                inst = case instToStripeParam of
                        SkipToStripeParam -> []
                        TopToStripeParam ->
                          [ instance' ((var "ToStripeParam") @@ (var (textToPascalName tyName)))
                                  [ funBinds "toStripeParam" [ match [ conP (fromString (textToPascalName $ tyName)) [ bvar "n" ] ]
                                                               ( var ":" @@ (tuple [string $ T.unpack tyName, var "toBytestring" @@ var "n"
                                                                                   ]) )
                                                             ]
                                  , funBinds "toStripeParamName" [ match [ wildP ] (string $ T.unpack tyName) ]
                                  ]
                          ]
                        _ -> []
            in ([], newtype' occName [] con (derivingCommon' gs) : inst, toStripeParamBuilder)
       else ([],[],toStripeParamBuilder)

  -- FIXME: should we use a Decimal type instead of Double?
  | (_schemaType s == Just OpenApiNumber) =
      let toStripeParamBuilder =
                    case instToStripeParam of
                      HelperToStripeParam path ->
                        let funName = T.concat (path ++ [tyName])
                        in [( funName
                            , funBind (fromString $ T.unpack funName)
                               (match [ bvar "n" ] (list [(tuple [string $ T.unpack $ mkKey (path ++ [tyName]), var "toBytestring" @@ var "n"])]))
                            )
                           ]
                      _ -> []
      in
       if wrapPrim
       then let occName = fromString (textToPascalName $ tyName)
                con = recordCon occName [ (textToCamelName $ "un_" <> tyName, field $ var "Double" ) ]
                inst = case instToStripeParam of
                         SkipToStripeParam -> []
                         TopToStripeParam ->
                                [ instance' ((var "ToStripeParam") @@ (var (textToPascalName tyName)))
                                   [ funBinds "toStripeParam" [ match [ conP (fromString (textToPascalName $ tyName)) [ bvar "n" ] ]
                                                               ( var ":" @@ (tuple [string $ T.unpack tyName, var "toBytestring" @@ var "n"
                                                                                   ]) )
                                                             ]
                                   , funBinds "toStripeParamName" [ match [ wildP ] (string $ T.unpack tyName) ]
                                   ]
                                ]
                         _ -> []
           in ([] , (newtype' occName [] con (derivingCommon' gs) : inst), toStripeParamBuilder )
      else ([],[], toStripeParamBuilder)

  | (_schemaType s == Just OpenApiBoolean) =
     let toStripeParamBuilder =
                    case instToStripeParam of
                      HelperToStripeParam path ->
                        let funName = T.concat (path ++ [tyName])
--                        in [(funName, valBind (fromString $ T.unpack funName) (var "id"))]
                        in [( funName
                            , funBind (fromString $ T.unpack funName)
--                               (match [conP (fromString (textToPascalName $ tyName)) [ bvar "n" ]] (var "id")))
                               (match [ bvar "n" ] (list [(tuple [string $ T.unpack $ mkKey (path ++ [tyName]), (if' (var "n") (string "true") (string "false"))])]))
                            )
                           ]
                      _ -> []

      in if wrapPrim
      then let occName = fromString (textToPascalName $ tyName)
               con = recordCon occName [ (textToCamelName $ "un_" <> tyName, field $ var "Bool" ) ]
               inst = case instToStripeParam of
                        SkipToStripeParam -> []
                        TopToStripeParam ->
                               [ instance' ((var "ToStripeParam") @@ (var (textToPascalName tyName)))
                                  [ funBinds "toStripeParam" [ match [ conP (fromString (textToPascalName $ tyName)) [ bvar "b" ] ]
                                                               ( var ":" @@ (tuple [string $ T.unpack tyName, (if' (var "b") (string "true") (string "false"))
                                                                      ]) )
                                                             ]
                                  , funBinds "toStripeParamName" [ match [ wildP ] (string $ T.unpack tyName) ]
                                  ]
                               ]
                        _ -> []

           in ([], (newtype' occName [] con (derivingCommon' gs)) : inst, toStripeParamBuilder)
      else ([],[],toStripeParamBuilder)

  | _schemaType s == Just OpenApiArray =
      case _schemaItems s of
        {-
        Just (OpenApiItemsObject (Ref (Reference r))) ->
          ([textToPascalName r], var "StripeList" @@ (var $ textToPascalName r), [])
        -}
        Just (OpenApiItemsObject (Inline si))
          | _schemaType si == Just OpenApiString ->
              case _schemaEnum si of
                Nothing ->
                  case _schemaType si of
                    (Just pty) | pty `elem`[ OpenApiBoolean, OpenApiInteger, OpenApiNumber, OpenApiString ] ->
                      let occName = fromString (textToPascalName $ tyName)
                          primTy = case pty of
                            OpenApiBoolean -> "Bool"
                            OpenApiInteger -> "Integer"
                            OpenApiNumber  ->
                              case _schemaFormat si of
                                (Just "float")  -> "Float"
                                (Just "double") -> "Double"
                                _               -> "Double"
                            OpenApiString -> "Text"
                          con = recordCon occName [(fromString $ "un" <> textToPascalName tyName, field $ listTy $ var primTy)]
                          ty = newtype' occName [] con (derivingCommon' gs)
                          json_o = mkFromJSON objName tyName s
                          (inst, builder) = case instToStripeParam of
                           SkipToStripeParam -> ([],[])
                           TopToStripeParam ->
                               ([ instance' ((var "ToStripeParam") @@ (var (textToPascalName tyName)))
                                  [ funBinds "toStripeParam" [ match [ conP (fromString (textToPascalName $ tyName)) [ bvar "xs" ] ]
                                                               (par (op (par ((var "map" @@ (lambda [ bvar "v" ] (tuple [ string (T.unpack $ tyName <> "[]"), (var "encodeUtf8" @@ var "v") ])) @@ (var "xs")))) "++" (var "")))
                                                             {-
                                                               ( var ":" @@ (tuple [string $ T.unpack tyName, (if' (var "b") (string "true") (string "false"))
                                                                      ]) )
-}
                                                             ]
                                  , funBinds "toStripeParamName" [ match [ wildP ] (string $ T.unpack tyName) ]
                                  ]
                               ], [ (tyName, funBind "foo" (match [] (var "error \"builder goes here\"")) )])
                           HelperToStripeParam path ->  -- if (tyName == "tiers") then error "do something here?" else ([],[])
                               let funName = T.concat (path ++ [tyName])
                                   builder' =
                                     [( funName
                                      , funBind (fromString $ T.unpack funName)
                                        (match [ bvar "txts" ]
                                         (let'  [funBind "mkTxt" (match [ bvar "txt" ] (tuple [string $ T.unpack $ mkKey (path ++ [tyName]) <> "[]", var "encodeUtf8" @@ var "txt" ]))]
                                         (var "map" @@ var "mkTxt" @@ var "txts")))
                                         -- (list [(tuple [string $ T.unpack $ mkKey (path ++ [tyName]), var "encodeUtf8" @@ var "txt" ])]))
                                      )
                                     ]
                               in ([], builder')

                      in ([], (ty : json_o : inst), builder) -- : concat decls
                (Just _) ->
                  let (ty_, decls, toStripeBuilderParamOne) = schemaToEnumDecl instToStripeParam objName tyName si
                      toStripeParamBuilderList =
                        case toStripeBuilderParamOne of
                          [one@(funName', builder')] ->
                            [ ( funName' <> "_list"
                              , funBind (fromString (T.unpack (funName'<>"_list")))
                                (match [ bvar "vs" ]
                                 (let' [builder']
                                   (var "concat" @@ (var "map" @@ var (fromString $ T.unpack funName') @@ var "vs")))
                                )
                              )]
                  in ([], decls, toStripeParamBuilderList)

        Just (OpenApiItemsObject (Inline s)) ->
          trace (T.unpack $ "We should probably actually do something here. inline - " <> tyName {- <> (show (ppSchema s)) -}) $
          let occName = fromString (textToPascalName tyName)
              (imports, decls, toStripeParamBuilder) = schemaToTypeDecls gs wrapPrim instToStripeParam objName tyName s
          in (imports, decls, toStripeParamBuilder)
--          in ([],[data' occName [] [ prefixCon (textToPascalName tyName) []] derivingCommon], [])
          {-
          let -- decls' = schemaToTypeDecls "FixMe4a" "FixMe4b" s
              entryTy = case _schemaTitle s of
                          (Just t) -> t
                          Nothing  -> "FixMeEntryTy"
{-
                            let (_,ty,_) = schemaToType gs objName tyName s -- error $ "schemaToTypeDecls - could not find schemaTitle for " ++ show (ppSchema s)
                            in ty
-}
              entryTyName = textToPascalName entryTy
              (entryImports, entryFields, entryDecls) =  unzip3 $ map (schemaToField gs wrapPrim (_schemaRequired s) tyName) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
              entryCon = recordCon entryTyName entryFields
              entryDecl = data' entryTyName [] [entryCon] (derivingCommon' gs)

              occName = fromString (textToPascalName $ tyName)


              con = recordCon occName [(fromString $ "un" <> textToPascalName tyName, field $ listTy $ var $ textToPascalName entryTy)]
          in (concat entryImports , entryDecl : (data' occName [] [con] (derivingCommon' gs)) : concat entryDecls) -- : concat decls
 -}
        _ -> trace (T.unpack $ "We should probably actually do something here. 1.     - " <> tyName {- <> (show (ppSchema s)) -}) $
                 ([], [], [])

    -- sometimes a property value is an Object, but the object has no predefined properties, so it is just a dictionary of key/value pairs.
    -- for example Konbini in SubscriptionsPost.PaymentSettings
  | (_schemaType s == Just OpenApiObject) && (null (_schemaProperties s)) =
      let occName   = fromString (textToPascalName tyName)
          conName   = fromString (textToPascalName tyName)
          unConName = fromString ("un" <> textToPascalName tyName)
          con       = recordCon occName [ ( unConName, field $ var "Object") ]
          json      = mkFromJSON objName tyName s
          toStripeParamBuilder =
                    case instToStripeParam of
                      HelperToStripeParam path ->
                        let funName = T.concat (path ++ [tyName])
                        in [( funName
                            , funBind (fromString $ T.unpack funName)
                                (match [ bvar "object" ] ( var "error" @@ string "toStripBuilder not unimplemented for Object yet." )
                                )
                            )]
      in ([], [ newtype' occName [] con [ deriving' [ var "Eq", var "Data", var "Ord", var "Read", var "Show" ]] , json ], toStripeParamBuilder)

    -- the assumption here is that we are generating a record for an object?
  | otherwise =
      let name =
            {- case tyName of
              "address" ->
                case objName of
                  "shipping" -> "shipping_address"
                  _          -> tyName
              _ -> -} withPrefixType objName tyName
          occName = fromString (textToPascalName name)
          instToStripeParam' = case instToStripeParam of
                                 (HelperToStripeParam path) -> (HelperToStripeParam (path ++ [name]))
                                 _                          -> (HelperToStripeParam [name])
          (imports, fields, decls, toStripeParamBuilders') =
            -- NOTE: we only want to wrap primitive values that are going to be used directly as parameters to operation calls. So we don't need to wrap prims that appear
            -- as fields in a record
            unzip4 $ map (schemaToField gs {- wrapPrim -} False instToStripeParam' (_schemaRequired s) name) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))

          inst = case instToStripeParam of
                   SkipToStripeParam -> []
                   TopToStripeParam ->
                     let varNms = [ "v" ++ show i | i <- [0 .. (length toStripeParamBuilders - 1)]]
                         toStripeParamBuilders = concat toStripeParamBuilders'
                     in -- if (name == "tiers") then (error $ show (length fields, map length toStripeParamBuilders')) else
                     [ instance' ((var "ToStripeParam") @@ (var (textToPascalName name)))
                       [ funBinds "toStripeParam" [ match [ conP (fromString (textToPascalName $ name)) (map (bvar . fromString) varNms ) ]
                                                    (let' (map snd toStripeParamBuilders) $
--                                                     par (op (list (map (\(f,v) -> (var (fromString $ T.unpack f) @@ (var $ fromString v))) (zip (map fst toStripeParamBuilders) varNms))) "++" (var "")))
                                                       par (op (par (var "concat" @@ (list (map (\(f,v) -> (var (fromString $ T.unpack f) @@ (var $ fromString v))) (zip (map fst toStripeParamBuilders) varNms))))) "++" (var "")))
                                                  ]
{-                                 [ {- funBinds "toStripeParam" [ match [ conP (fromString (textToPascalName $ tyName)) [ bvar "b" ] ]
                                                               ( var ":" @@ (tuple [string $ T.unpack tyName, (if' (var "b") (string "true") (string "false"))
                                                                      ]) )
                                                             ] -} ] -}
                       , funBinds "toStripeParamName" [ match [ wildP ] (string $ T.unpack tyName) ]
                       ]
                     ]
                   _ -> []
          con  = recordCon occName fields
          json = mkFromJSON objName name s

          toStripeParamBuilder =
                    case instToStripeParam of
                      HelperToStripeParam path ->
--                        concat toStripeParamBuilders'
                        let funName = T.concat (path ++ [tyName])
                            varNms = [ (T.unpack tyName) ++ "_v" ++ show i | i <- [0 .. (length toStripeParamBuilders' - 1)]]
                            matchc = (match [ conP (fromString (textToPascalName (withPrefixType objName tyName))) (map (bvar . fromString) varNms ) ]
                                 (let' (map snd (concat toStripeParamBuilders')) $
                                   ( (par (var "concat" @@ (list (map (\(f,v) -> (var (fromString $ T.unpack f) @@ (var $ fromString v))) (zip (map fst (concat toStripeParamBuilders')) varNms))))) ))
                               )
                        in [( funName
                            , funBind (fromString $ T.unpack funName)
                               (if isEmptyable s
                                 then (match [ bvar "mc" ]
                                        (case' (var "mc")
                                         [ match [ conP "Empty" [] ] (list [ tuple [ string $ T.unpack $ mkKey (path ++ [tyName]), string "" ] ] )
                                         , match [ conP "Full" [ bvar "c"] ] (case' (var "c") [ matchc ])
                                         ]
                                        )
                                      )
                                 else matchc
                               )
                            )
                           ]
                      _ -> []

      in case gs of
           AllDeclarations -> (concat imports, (data' occName [] [con] (derivingCommon' gs))  : (json : inst ++ concat decls), toStripeParamBuilder)
           HsBoot -> ([]
                     , data' occName [] [] [] :
                       (instance' (var "FromJSON" @@ var (textToPascalName name)) []) :
                          [instance' (var n @@ var (textToPascalName name)) [] | n <- derivingNames ]
                     , []
                     )

isRequired :: Schema -> ParamName -> Bool
isRequired s p = p `elem` (_schemaRequired s)

referencedParamToDecl :: Referenced Param -> HsDecl'
referencedParamToDecl (Inline p) =
  paramToDecl p
{-
  let occName = textToPascalName $ _paramName p
  in data' occName [] (paramToConDecls (_paramName p) (_paramSchema p)) derivingCommon
-}

paramToConDecls :: Text -> Schema -> [ConDecl']
paramToConDecls tyName schema
  | _schemaType schema == Just OpenApiString =
      case _schemaEnum schema of
        (Just enums) ->
          let occNam = textToPascalName tyName
          in [ prefixCon (fromString $ pascal $ T.unpack c) [] | (Aeson.String c) <- enums ]
        _ -> []
  | otherwise = []

paramToDecl :: Param -> HsDecl'
paramToDecl p =
  let occName = textToPascalName $ _paramName p
      schema = case _paramSchema p of
        (Just (Inline s)) -> s
        _ -> error $ "paramToDecl: unabled to handle schema for: " ++ show (ppParam p)
  in data' occName [] (paramToConDecls (_paramName p) schema) derivingCommon

subscriptionSchema :: OpenApi -> Schema
subscriptionSchema o =
  case InsOrd.lookup "subscription" (_componentsSchemas (_openApiComponents o)) of
    Nothing -> error "could not find subsription schema"
    (Just s) -> s

componentSchemaByName :: OpenApi -> Text -> Schema
componentSchemaByName o n =
  case InsOrd.lookup n (_componentsSchemas (_openApiComponents o)) of
    Nothing -> error $ "could not find schema for " <> T.unpack n
    (Just s) -> s

data Method = GET | POST | DELETE
  deriving (Eq, Ord, Read, Show)
{-
mkParamName :: Param -> RdrNameStr
mkParamName p =
  case _paramName p of
    "expand" -> fromString "ExpandParams"
    -- things which are actually IDs
    n | n `elem` ["charge"] -> fromString $ textToPascalName (n <> "_id")
    n        -> fromString $ textToPascalName n
-}

data NameStyle = Pascal | Camel deriving (Eq, Ord, Read, Show)

-- FIXME: the list of things which are actually IDs should be computed, not hard coded
mkParamName :: (IsString s) => NameStyle -> Text -> ([(RdrNameStr, [RdrNameStr])],  s)
mkParamName s p =
  case p of
    "expand" -> ([], fromString "ExpandParams")
    -- things which are actually IDs
    n | n `elem` ["charge", "customer"] ->
          ([(fromString ("Component." <> textToPascalName n), [ textToPascalName (n <> "_id")])], fromString $ textToName (n <> "_id"))
    n        -> ([], fromString $ textToName n)

  where
    textToName
      | s == Camel = textToCamelName
      | s == Pascal = textToPascalName
{-
mkToStripeParam paramNm =
  instance' (var "ToStripeParam" @@  (var paramNm))
    [ funBinds "toStripeParam" [ match [ conP (mkParamName Pascal $ _paramName param) [ bvar "v" ] ] (var "id") ]
  -}
mkStripeHasParam :: OccNameStr
                 -> Maybe Text
                 -> Referenced Param
--                 -> (RdrNameStr, [HsDecl'])
                 -> (Maybe ParamName, (Maybe (NonEmpty String), [(RdrNameStr, [RdrNameStr])], [HsDecl'], InsOrdHashMap Text [HsDecl']))
mkStripeHasParam opName mIdName (Inline param) =
  let paramNm =  case _paramName param of
                   "address" {- | opName == "CustomersPost" -} -> "customer_address"
                   pn -> pn
      req = case _paramRequired param of
              (Just True) -> Just paramNm
              _           -> Nothing
  in (req, mkStripeHasParamFromProperty (NonEmpty.singleton "modBaseName") opName (paramNm, (fromJust (_paramSchema param))))
{-
  in if paramNm `elem` ["StartingAfter", "EndingBefore"]
     then case mIdName of
            Nothing -> error $ "mkStripeHasParam: expect an idName but got Nothing. opName = " ++ show opName ++ " , param = " ++ show (ppParam param)
            (Just idName) -> (textToPascalName idName, [ instance' (var "StripeHasParam" @@ (var $ UnqualStr opName) @@ (var paramNm @@ (var $ textToPascalName idName))) []])
     else (paramNm, [ instance' (var "ToStripeParam" @@  (var paramNm))
                       [ funBinds "toStripeParam" [ match [ conP (mkParamName Pascal $ _paramName param) [ bvar "v" ] ] (var "id") ] ]
                    , instance' (var "StripeHasParam" @@ (var $ UnqualStr opName) @@ (var $ paramNm)) []
                    ])
-}
needsOwnModule :: Schema -> Bool
needsOwnModule s =
  (not $ InsOrd.null (_schemaProperties s)) ||
  (not $ null $ _schemaItems s)
{-
mkToStripeParam :: Text -> Schema -> HsDecl'
mkToStripeParam pName schema =
  let pn = mkParamName Pascal pName
  in instance' (var "ToStripeParam" @@ (var pn)) []
-}
mkStripeHasParamFromProperty :: NonEmpty String -- ^ module name -- just the last bit like 'Account'
                             -> OccNameStr
                             -> (Text, (Referenced Schema))
                             -> (Maybe (NonEmpty String), [(RdrNameStr, [RdrNameStr])], [HsDecl'], InsOrdHashMap Text [HsDecl'])
mkStripeHasParamFromProperty modBaseName opName (pName, r@(Inline schema)) =
      if | isAnyOfRangeQuerySpec schema ->
             let (pimports, pn) = mkParamName Pascal pName
                 decls = [ data' (snd $ mkParamName Pascal pName) [] [ prefixCon (snd $ mkParamName Pascal pName) [ strict $ field $ var "UTCTime" ] ] derivingCommon ]
                 insts = [ instance' (var "StripeHasParam" @@ (var $ UnqualStr opName) @@ (var pn)) []
                         , instance' (var "StripeHasParam" @@ (var $ UnqualStr opName) @@ (var "TimeRange" @@ (var pn))) []
                         , instance' (var "ToStripeParam" @@ (var pn ))
                           [ funBinds "toStripeParam" [ match [ conP pn [ bvar "t" ] ]
                                                               ( var ":" @@ (tuple [string $ T.unpack pName
                                                                                   , var "toBytestring" @@ (var "toSeconds" @@ var "t")
                                                                                   ]) )
                                                             ]
                           , funBinds "toStripeParamName" [ match [ wildP ] (string $ T.unpack pName) ]
                           ]
                         ]
             in (Nothing , {- FIXME: this does not work because the module path is prepended. [(fromString "Web.Stripe.Types", [fromString "TimeRange"]) ] -} [], decls ++ insts, InsOrd.empty)

         | otherwise ->
             let pName' = case pName of
                            "address" | opName == "PostCustomers" -> "customer_address"
                            "name" | opName == "PostCustomers" -> "customer_name"
                            _ -> pName
                 (pimports, pn) = mkParamName Pascal pName'
                 mkEmptyable v =
                   if isEmptyable schema then var "Emptyable" @@ v else v
                 insts = (instance' (var "StripeHasParam" @@ (var $ UnqualStr opName) @@ (mkEmptyable $ var pn)) []) :
                      (if pn `elem` [ "Metadata" ] then [] else [{- mkToStripeParam pName schema -}])
                 (imports, decls, toStripeParamBuilder) = schemaToTypeDecls AllDeclarations True TopToStripeParam "" pName' schema
                 tys = InsOrd.fromList [(pName', decls)]
                 (ownMod, ownModImports)
                      | needsOwnModule schema =
                          (Just $ modBaseName <> (NonEmpty.singleton $ textToPascalName pName), [(fromString $ foldr1 (\a b -> a <> "." <> b) modBaseName, [ (UnqualStr opName) ])])
                      | otherwise = (Nothing, [])
             in (ownMod , pimports ++ ownModImports ++ imports, insts, tys)

mkStripeRequestBodyStripeHasParam :: NonEmpty String -- ^ module name -- just the last bit like 'Account'
                                  -> OccNameStr
                                  -> Maybe (Referenced RequestBody)
                                  -> ([ParamName], [(Maybe (NonEmpty String), [(RdrNameStr, [RdrNameStr])], [HsDecl'], InsOrdHashMap Text [HsDecl'])])
mkStripeRequestBodyStripeHasParam _ opName Nothing = ([], [])
mkStripeRequestBodyStripeHasParam modBaseName opName (Just (Inline rb)) =
  case InsOrd.lookup "application/x-www-form-urlencoded" (_requestBodyContent rb) of
    Nothing -> ([], [])
    (Just mto) ->
      case _mediaTypeObjectSchema mto of
        (Just (Inline schema)) ->
          (_schemaRequired schema, map (mkStripeHasParamFromProperty modBaseName opName) (InsOrd.toList (_schemaProperties schema )))


responseType :: Response -> ([(RdrNameStr, [RdrNameStr])], HsType')
responseType resp =
  case InsOrd.lookup "application/json" (_responseContent resp) of
    Nothing -> error $ "responseType: could not find application/json for response " <> show (ppResponse resp)
    (Just mto) ->
      case _mediaTypeObjectSchema mto of
        (Just (Inline schema)) ->
          case InsOrd.lookup "data" (_schemaProperties schema) of
            (Just (Inline dataSchema)) ->
              case _schemaItems dataSchema of
                (Just (OpenApiItemsObject itemTypeSchema)) ->
                  let (imports, ty, _) = referencedSchemaToType AllDeclarations "FixMeResponseType1" "FixMeResponseType" itemTypeSchema
                  in (imports, var "StripeList" @@ ty)
            Nothing ->
              case _schemaAnyOf schema of
                (Just anyOf) ->
                  ([], var "OneOf" @@ (listPromotedTy $ map (\(Ref (Reference s)) -> var $ textToPascalName s) anyOf))
                Nothing ->
                  do error $ "Could not find schemaProperty named 'data'\n " <> show (ppSchema schema)
        (Just (Ref (Reference s))) ->
          ([(fromString $ "Component." <> textToPascalName s, [textToPascalName s])], var (textToPascalName s))

data PathTemplate
   = PathStatic Text
   | PathSubst Text
   deriving (Eq, Ord, Show)

extractTemplate :: Text -> [PathTemplate]
extractTemplate txt | T.null txt = []
extractTemplate txt =
  case T.break (== '{') txt of
    (static, rest)
      | T.null rest -> [PathStatic static]
      | otherwise ->
          let (subst, rest') = T.break (== '}') (T.drop 1 rest)
          in PathStatic static : PathSubst subst : extractTemplate (T.drop 1 rest')

mkPathTemplate :: Maybe Text -> PathTemplate -> (Maybe (Pat', HsType'), HsExpr')
mkPathTemplate _ (PathStatic static) = (Nothing, string (T.unpack static))
mkPathTemplate mIdName (PathSubst subst)   =
  -- the path substitutions are typically IDs, but the spec is sometimes ambiguous about
  -- the type of the id value. We explicit map a few values, and infer the remaining ones
  let name =
        case subst of
          "id" -> case mIdName of
                    Nothing -> "mkPathTemplate: expected an idName but got Nothing"
                    (Just idName) -> idName
          "fee" -> "ApplicationFeeId" -- probably?
          _    -> subst <> "_id"
  in
    ( Just ( bvar (textToCamelName name)
           , var (textToPascalName name)
           )
    , var (textToCamelName ("un_" <> name)) @@ var (textToCamelName name)
    )

mkUrl :: Maybe Text -> [PathTemplate] -> ([(Pat', HsType')], HsExpr')
mkUrl _ [] = error "mkUrl: Can't create something from nothing."
mkUrl idName [pt] =
  case mkPathTemplate idName pt of
    (Nothing, exp) -> ([], exp)
    (Just (pat, typ), exp) ->
      ([(pat, typ)], exp)
mkUrl idName (pt:pts) =
  let (mPatTy, expl) = mkPathTemplate idName pt
      (patTys, expr) = mkUrl idName pts
      patTys' = case mPatTy of
        Nothing -> patTys
        (Just patTy) -> (patTy:patTys)
  in (patTys', op expl "</>" expr)

-- for the specified Operation, create a function that creates a `StripeRequest`
mkRequestDecl :: FilePath -> Method -> Maybe Text -> Operation -> [ParamName] -> ([(RdrNameStr, [RdrNameStr])], [HsDecl'], [RdrNameStr])
mkRequestDecl path method idName oper requiredParams =
  let opName :: OccNameStr
      opName   = textToCamelName $ fromJust $ _operationOperationId oper

      opName' :: RdrNameStr
      opName'  = textToPascalName $ fromJust $ _operationOperationId oper

      request = valBind "request" (var "mkStripeRequest" @@ var (fromString $ show method) @@ var "url" @@ var "params")
      pathTemplate = extractTemplate (T.pack path)
      (patTys, urlE) = mkUrl idName pathTemplate
--      (pats, typs) :: ([Pat'], [HsType'])
      requiredParamTypes   = map (var . snd . mkParamName Pascal) requiredParams
      requiredParamImports = [] -- map (\p -> (fromString ("Component." <> (textToPascalName p)), [ snd $ mkParamName Pascal p])) (requiredParams \\ webStripeTypesNames)
      requiredParamPats :: [Pat']
      requiredParamPats   = map (bvar . snd . mkParamName Camel) requiredParams
      requiredParamVars :: [HsExpr']
      requiredParamVars   = map (var . snd . mkParamName Camel) requiredParams
      (pats, typs) = unzip patTys
      url = valBind "url" urlE

      ty :: HsType'
      ty = foldr (\a b -> a --> b) (var "StripeRequest" @@ var opName') (requiredParamTypes ++ typs)

      {-
      mkUrlFromPaths :: [FilePath] -> HsExpr'
      mkUrlFromPaths [p] = string p
      mkUrlFromPaths (p:ps) = op (string p) "</>" (mkUrlFromPaths ps)

      (pats, url)     =
        case splitPath path of
          [] -> error $ "mkRequestDecl: surely the path can't be empty?"
          ps -> extractTemplate (pats, valBind "url" (mkUrlFromPaths ps))
      -}
      params  = valBind "params" (foldr (\v l -> (var "toStripeParam") @@ v @@ l) (var "[]") requiredParamVars)
  in  (requiredParamImports
      , [ typeSig opName ty
        , funBind opName (matchGRHSs (requiredParamPats ++ pats) (rhs (var "request") `where'` [request, url, params]))
        ]
      , [ opName', textToCamelName $ fromJust $ _operationOperationId oper ]
      )
{-
mkOperationTypes :: ((NonEmpty String), [(RdrNameStr, [RdrNameStr])], [HsDecl'], InsOrdHashMap Text [HsDecl'])
                 -> ((NonEmpty String), [(RdrNameStr, [RdrNameStr])], [HsDecl'], [RdrNameStr]) -- ^ (imports, decls, re-exports, new things to export)
mkOperationTypes (modBaseName, decls) =
  let (_, paramImports, instanceDecls, typeDecls) = unzip4 decls

      -- extract the various types
      typeDecls' :: [HsDecl']
      typeDecls' = concatMap snd $ concatMap InsOrd.toList typeDecls

      -- used as part of creating an explicit export list?
--      reexports =  map (mkParamName Pascal . fst) $ concatMap InsOrd.toList typeDecls
  in (modBaseName, paramImports, instanceDecls, typeDecls')
-}

{-
For GET requests, the params come from _operationParameters.
For POST requests the params come from _operationRequestBody.

Not sure if POST requests also have operationParameters
-}
mkOperation :: NonEmpty String -- ^ module name -- just the last bit like 'Account'
            -> FilePath        -- ^ path
            -> Method          -- ^ method
            -> Maybe Text      -- ^ what type is {id}
            -> Operation
            -> [(Maybe (NonEmpty String), ([(RdrNameStr, [RdrNameStr])], [HsDecl'], [RdrNameStr]))] -- ^ (imports, decls, re-exports, new things to export)
mkOperation modBaseName path method mIdName op =
  let opName :: OccNameStr
      opName   = textToPascalName $ fromJust $ _operationOperationId op

      -- create a constructorless type for use as the phantom type parameter to StripeRequest
      opIdDecl = data' opName [] [] []

      -- create all the  StripeHasParam instances for params that appear in the RequestBody of this operation
      (requiredParams, decls) = mkStripeRequestBodyStripeHasParam modBaseName opName (_operationRequestBody op)
      (thisModDecls, ownModDecls) = partition (\(m,_,_,_) -> isNothing m) decls
      (_, paramImports, instanceDecls, typeDecls) = unzip4 thisModDecls

      typeDecls' :: [HsDecl']
      typeDecls' = concatMap snd $ concatMap InsOrd.toList typeDecls

      reexports =  map (snd . mkParamName Pascal . fst) $ concatMap InsOrd.toList typeDecls

      inQuery :: Referenced Param -> Bool
      inQuery (Inline p) = (_paramIn p) == ParamQuery

      -- create all the  StripeHasParam instances for params that appear in the Query of this operation
      (requiredParamsOP, declsOP) = unzip $ map (mkStripeHasParam opName mIdName) $ filter inQuery (_operationParameters op)
      (thisModDeclsOP, ownModDeclsOP) = partition (\(m,_,_,_) -> isNothing m) declsOP
      (_, paramImportsOP, instanceDeclsOP, typeDeclsOP) = unzip4 thisModDeclsOP

      typeDeclsOP' :: [HsDecl']
      typeDeclsOP' = concatMap snd $ concatMap InsOrd.toList typeDeclsOP


      stripeHasParamDecls = (concat instanceDecls) ++ typeDecls' ++ (concat instanceDeclsOP) ++ typeDeclsOP'

      (returnImports, returnTy) =
            case InsOrd.lookup 200 (_responsesResponses (_operationResponses op)) of
              (Just (Inline resp)) -> responseType resp

      (requestDeclImports, requestDecl, requestTypes) = mkRequestDecl path method mIdName op (requiredParams ++ (catMaybes requiredParamsOP))

      stripeReturnDecl = tyFamInst "StripeReturn" [var $ UnqualStr opName] returnTy

--      mkEnums AllDeclarations name (findEnums' component Map.empty)p

--      map referencedParamToDecl (_operationParameters $ fromJust $ _pathItemPost pi)
      addIdName =
        case mIdName of
          Nothing -> id
          (Just idName) -> (textToPascalName idName :)
          -- FIXME: this nub should really combine and nub all imports from the same module into a single import
  in (Nothing, (nub (sort (requestDeclImports ++ returnImports ++ concat paramImports ++ nub (concat paramImportsOP) )), (requestDecl ++ (opIdDecl:stripeReturnDecl:stripeHasParamDecls)), [] )) :
     (map (\(mModBase, pathImports, instanceDecls, typeDecls) -> (mModBase, (pathImports, (concatMap snd $ InsOrd.toList typeDecls) ++ instanceDecls, []))) ownModDecls)


--  in [(modBaseName, (concat paramImports, (requestDecl ++ (opIdDecl:stripeReturnDecl:stripeHasParamDecls)),  {- addIdName ((map fst returnImports) ++ params ++ reexports), -} [] {- requestTypes FIMXE -}))]


{-
-- create Web.Stripe.Account module
mkAccount :: OpenApi -> IO ()
mkAccount s =
  do let path = "/v1/account"
         (Just pi) = InsOrd.lookup path (_openApiPaths s)
         (Just op) = _pathItemGet pi
         (opDecls, _, additionalExports) = mkOperation path "GET" op
     let reexportTypes = [ thingAll "Account"
                         , thingAll "AccountId"
                         ]

         imports = [ import' "Web.Stripe.StripeRequest" `exposing`
                     [ thingWith "Method" ["GET"]
                     , thingAll "StripeRequest"
                     , var "StripeReturn"
                     , var "mkStripeRequest" ]
                   , import' "Web.Stripe.Types" `exposing` reexportTypes
                   ]
         exports = Just (reexportTypes ++ (map var additionalExports))
         modul  = module' (Just $ "Web.Stripe.Account") exports imports opDecls
         extensions = [ FlexibleInstances
                      , MultiParamTypeClasses
                      , OverloadedStrings
                      , TypeFamilies
                      ]
     formatted <- showModule "Web/Stripe/Account.hs" extensions modul True
     T.putStr formatted
     createDirectoryIfMissing True "_generated/src/Web/Stripe"
     T.writeFile "_generated/src/Web/Stripe/Account.hs" formatted
     pure ()
-}


unzip4   :: [(a,b,c,d)] -> ([a],[b],[c],[d])
{-# INLINE unzip4 #-}
-- Inline so that fusion `foldr` has an opportunity to fire.
-- See Note [Inline @unzipN@ functions] in GHC/OldList.hs.
unzip4   =  foldr (\(a,b,c,d) ~(as,bs,cs,ds) -> (a:as,b:bs,c:cs,d:ds))
                  ([],[],[],[])

unzip3Concat :: [([a],[b],[c])] -> ([a],[b],[c])
unzip3Concat l =
  let (as, bs, cs) = unzip3 l
  in (concat as, concat bs, concat cs)

unzip4Concat :: [([a],[b],[c],[d])] -> ([a],[b],[c],[d])
unzip4Concat l =
  let (as, bs, cs, ds) = unzip4 l
  in (concat as, concat bs, concat cs, concat ds)


lookupPaths :: InsOrdHashMap FilePath PathItem -> [(FilePath, Maybe Text)] -> [PathItem]
lookupPaths hash [] = []
lookupPaths hash ((p,_) : ps) =
  case InsOrd.lookup p hash of
    (Just pi) -> pi : lookupPaths hash ps
    Nothing -> error $ "lookupPaths: could not find path " ++ p

-- mkImport :: RdrNameStr -> IE'
mkImport (n, things) =  import' (fromString $ "Web.Stripe."  <> (rdrNameStrToString n)) `exposing` [ thingWith thing [] | thing <- things ]

mkOwnMods :: (Maybe (NonEmpty String), ([(RdrNameStr, [RdrNameStr])], [HsDecl'], [RdrNameStr]) ) -> IO ()
mkOwnMods (Just modBaseName, decls) =
  let (pathImports, opDecls, additionalExports) = decls
  in  mkPathModule modBaseName pathImports opDecls Nothing -- additionalExports

mkPathModule :: NonEmpty String -> [(RdrNameStr, [RdrNameStr])] -> [HsDecl'] -> Maybe [RdrNameStr] -> IO ()
mkPathModule modBaseName pathImports decls exports' =
  do let imports = [ import' "Control.Applicative" `exposing` [ var "pure", var "(<$>)", var "(<*>)", var "(<|>)" ]
                   , import' "Control.Monad" `exposing` [ var "mzero" ]
                   , qualified' $ import'  "Data.Aeson"
                   , import' "Data.Aeson" `exposing` [ thingWith "FromJSON" [ "parseJSON" ]
                                                     , thingAll "ToJSON"
                                                     , thingWith "Value" [ "String", "Object", "Bool" ]
                                                     , var "Object"
                                                     , var "(.:)"
                                                     , var "(.:?)"
                                                     -- , var "Object"
                                                     ]
                   , qualified' $ import' "Data.Aeson" `as'` "Aeson"
                   , import' "Data.Data" `exposing` [ var "Data", var "Typeable" ]
                   , import' "Data.Map"   `exposing` [ var "Map" ]
                   , import' "Data.Time.Clock" `exposing` [ var "UTCTime" ]
                   , import' "Data.Text" `exposing` [ var "Text", var "unpack" ]
                   , import' "Data.Text.Encoding" `exposing` [ var "encodeUtf8" ]
                   , import' "Web.Stripe.StripeRequest" `exposing`
                       [ thingAll "Method"
                       , thingWith "StripeHasParam" []
                       , thingAll "StripeRequest"
                       , thingAll "ToStripeParam"
                       , var "StripeReturn"
                       , var "mkStripeRequest"
                       ]
                   , import' "Web.Stripe.Types" `exposing`
                        [ -- thingAll "Amount"
                          thingWith "Currency" []
--                        , thingAll "Created"
                        , thingAll "TimeRange"
                        , thingAll "Emptyable"
                        , thingAll "Expandable"
                        , thingAll "ExpandParams"
                        , thingAll "Metadata"
                        , thingAll "StripeList"
                        , thingAll "UpTo"
--                        , thingAll "StartingAfter"
--                        , thingAll "EndingBefore"
--                        , thingAll "Limit"
                        , thingAll "NowOrLater"
                        , var "ExpandsTo"
                        ]
                   , import' "Web.Stripe.OneOf" `exposing`
                      [ thingAll "OneOf"
                      ]
                   , import' "Web.Stripe.Util" `exposing` [ var "(</>)"
                                                          , var "toBytestring"
                                                          , var "toSeconds"
                                                          ]
                   ] ++ (map mkImport ({- propImports ++ -} pathImports))
         exports = Nothing
         modul  = module' (Just $ fromString $ "Web.Stripe." <> foldr1 (\a b -> a <> "." <> b) modBaseName) exports imports decls
         extensions = [ DataKinds
                      , DeriveDataTypeable
                      , FlexibleInstances
                      , MultiParamTypeClasses
                      , OverloadedStrings
                      , OverlappingInstances
                      , StandaloneDeriving
                      , TypeFamilies
                      ]
     formatted <- showModule ("Web/Stripe/" <> foldr1 (\a b -> a <> "/" <> b) modBaseName <> ".hs") extensions modul False
--     T.putStr formatted
     let filepath = "_generated/src/Web/Stripe/" <> foldr1 (\a b -> a <> "/" <> b) modBaseName <> ".hs"
     createDirectoryIfMissing True (takeDirectory filepath)
     T.writeFile filepath formatted
     pure ()

mkPaths :: OpenApi -- ^ openapi spec
        -> [(FilePath, Maybe Text)]    -- ^ path (e.g. \/v1\/account), what type is '{id}' in the path
        -> NonEmpty String    -- ^ module name -- just the last bit like 'Account'
        -> IO ()
mkPaths oa paths modBaseName =
  do {- let (thisMod, ownMods') = partition (isNothing . fst) $ concatMap (mkPath oa modBaseName) paths
         ownsMods' = Map.toList $ Map.fromListWith (<>) ownMods'
         (pathImports, opDecls, {- reexportTypes, -} additionalExports) = unzip3Concat $ map snd thisMod
     mkPathModule modBaseName pathImports opDecls Nothing
     mapM_ mkOwnMods ownMods'
     -}
     mapM_ (mkPath oa modBaseName) paths
     pure ()

mkPath :: OpenApi
       -> NonEmpty String    -- ^ module name -- just the last bit like 'Account'
       -> (FilePath, Maybe Text)
       -> IO () -- [(Maybe (NonEmpty String), ([(RdrNameStr, [RdrNameStr])], [HsDecl'], [RdrNameStr]))]
mkPath oa modBasePath (path, idName) =
  do mkPath' oa modBasePath GET  (path, idName) -- <>
     mkPath' oa modBasePath POST (path, idName)
{-
mkPath oa (path, idName) =
  let (Just pi) = InsOrd.lookup path (_openApiPaths oa)
      (Just op) = _pathItemGet pi
      (opDecls, reexports, additionalExports) = mkOperation path "GET" idName op
      reexportTypes = map thingAll (nub reexports)
{-
      imports = [ import' "Web.Stripe.StripeRequest" `exposing`
                     [ thingWith "Method" ["GET"]
                     , thingAll "StripeRequest"
                     , var "StripeReturn"
                     , var "mkStripeRequest" ]
                   , import' "Web.Stripe.Types" `exposing` reexportTypes
                   ]
-}
      exports = Just (reexportTypes ++ (map var additionalExports))
  in (opDecls, reexportTypes, additionalExports)
-}
mkPath' :: OpenApi
        -> NonEmpty String    -- ^ module name -- just the last bit like 'Account'
        -> Method
        -> (FilePath, Maybe Text)
        -> IO () -- [(Maybe (NonEmpty String), ([(RdrNameStr, [RdrNameStr])], [HsDecl'], [RdrNameStr]))]
mkPath' oa modBaseName' method (path, idName) =
  let (Just pi) = InsOrd.lookup path (_openApiPaths oa)
      modBaseName =
        case modBaseName' of
          (hd :| tl) -> (hd <> (case method of GET -> "Get" ; POST -> "Post")) :| tl

      mop = case method of
                    GET  -> _pathItemGet pi
                    POST -> _pathItemPost pi
  in case mop of
       Nothing   -> pure ()
       (Just op) ->
         do let (thisMod, ownMods') = partition (isNothing . fst) $ mkOperation modBaseName path method idName op
                ownsMods' = Map.toList $ Map.fromListWith (<>) ownMods'
                (pathImports, opDecls, {- reexportTypes, -} additionalExports) = unzip3Concat $ map snd thisMod
            mkPathModule modBaseName pathImports opDecls Nothing
            mapM_ mkOwnMods ownMods'
{-
        Nothing -> ([],[],[])
        (Just op) ->
          let (imports, opDecls, additionalExports) = mkOperation modBasePath path method idName op
--              reexportTypes = map thingAll (nub reexports)
--              exports = Just ({- reexportTypes ++ -} (map var additionalExports))
          in (imports, opDecls, additionalExports)  -- FIXME: we used to define all the types in Web.Stripe.Types, but now some are defined locally
-}

{-
      imports = [ import' "Web.Stripe.StripeRequest" `exposing`
                     [ thingWith "Method" ["GET"]
                     , thingAll "StripeRequest"
                     , var "StripeReturn"
                     , var "mkStripeRequest" ]
                   , import' "Web.Stripe.Types" `exposing` reexportTypes
                   ]
-}

needsMkJSON :: Schema -> Bool
needsMkJSON s =
  case _schemaType s of
    Nothing -> True
    (Just ts) -> not $ ts `elem` [ OpenApiBoolean, OpenApiInteger, OpenApiNumber, OpenApiString  ]

mkFromJSON :: Text -> Text -> Schema -> HsDecl'
mkFromJSON objName name s =
  -- the the schema an AnyOf?
  case _schemaAnyOf s of
    (Just schemas) ->
      instance' (var "FromJSON" @@ (var $ textToPascalName name))
         [ funBinds "parseJSON" [ match [wildP] (var "error" @@ (op (string "fromJSON = ") "++" (string $ T.unpack name))) ]
         ]
    Nothing ->
      -- is the schema an Enum?
      case _schemaEnum s of
        (Just vs) ->
          let mkConName :: (IsString a) => Text -> a
              mkConName c
                | T.isSuffixOf "version" name  = textToPascalName ("V" <> c) -- maybe instead of looking at the type suffix, which should look if the constructor starts with a number
                | otherwise         = textToPascalName (withPrefixEnumCon objName name c)
              mkEmptyable ty = if elem (Aeson.String "") vs then var "Emptyable" @@ ty else ty
              mkMatch v
                | isEmptyable s =
                  case v of
                    "" -> match [ string "" ] (var "pure" @@ var "Empty")
                    _  -> match [ string (T.unpack v) ] (var "pure" @@ (var "Full" @@ var (mkConName v)))
                | otherwise     = match [ string (T.unpack v) ] (var "pure" @@ var (mkConName v))



          in
          instance' (var "FromJSON" @@ (mkEmptyable (var $ textToPascalName (withPrefixType objName name))))
             [ funBinds "parseJSON" [ match [conP "String" [bvar "c"]] $
                                              case' (var "c")
                                                ([ mkMatch v | (Aeson.String v) <- vs ] ++
                                                 [ match [ bvar "s" ] (var "fail" @@ ( op (string "Failed to parse JSON value ") "++" (var "unpack" @@ var "s"))) ])
                                    , match [bvar "j"] (var "fail" @@ ( op (string "Failed to parse JSON value ") "++" (var "show" @@ var "j")))
                                    ]
             ]

        Nothing ->
          -- is it a list of items?
          case _schemaItems s of
            Just (OpenApiItemsObject o) ->
              instance' (var "FromJSON" @@ (var $ textToPascalName name))
                [ funBinds "parseJSON" [ match [ bvar "j" ] (op' (var $ textToPascalName name) "<$>" ((var "parseJSON") @@ (var "j"))) ]
                ]
            Nothing ->
--              if (name == "preferred_locales") then (trace (show $ ppSchema s)) else id $
              let properties = sortOn fst $ (InsOrd.toList (_schemaProperties s))
              in instance' (var "FromJSON" @@ (var $ textToPascalName name))
                [ funBinds "parseJSON" [ match [bvar "(Data.Aeson.Object o)"] $
                              case properties of
                                -- FIXME: the [] case probably happens when there are only additionalPropreties -- aka a dictionary of key/value pairs where th
                                -- the additionlProperties are the key names
                                [] -> var "pure" @@ ((var $ textToPascalName name) @@ (var "o")) -- (var "pure") @@ (var "undefined") --  (var $ textToPascalName name)  -- FIXME
                                _  -> op' (var $ textToPascalName name) "<$>" $ addAp $ map (mkJsonField name (_schemaRequired s)) $ properties
                                                    ]
                , funBinds "parseJSON" [ match [wildP] (var "mzero") ]
                ]

op' :: HsExpr' -> RdrNameStr -> HsExpr' -> HsExpr'
op' x o y =
  OpApp  EpAnnNotUsed (mkLocated x) (mkLocated $ var o) (mkLocated y)

addAp :: [HsExpr'] -> HsExpr'
addAp [a] = a
addAp (a:rs) =  (op' a "<*>" (addAp rs))

mkJsonField :: Text -> [Text] -> (Text, Referenced Schema) -> HsExpr'
-- mkJsonField objName ("amount", (Inline s)) = par (op' (var "Amount") "<$>" (op (var "o") ".:"  (string "amount")))
-- mkJsonField objName ("amount_refunded", (Inline s)) = par (op' (var "Amount") "<$>" (op (var "o") ".:"  (string "amount_refunded")))
mkJsonField objName requiredFields ("object", (Inline s)) =
  op (var "o") ".:" (string "object")
mkJsonField objName requiredFields ("id", (Inline s))
  | not ("id" `elem` requiredFields) &&  (not $ null requiredFields) =
    par (op' (var "fmap" @@ (var (textToPascalName $ objName <> "_id"))) "<$>" (op (var "o") ".:?"  (string "id")))
  | otherwise =
    par (op' (var (textToPascalName $ objName <> "_id")) "<$>" (op (var "o") ".:"  (string "id")))
mkJsonField _ requiredFields (fieldName, (Inline s)) =
  let oper = if ((Just True == _schemaNullable s) || ((not $ null requiredFields)  && (not $ fieldName `elem` requiredFields)))
             then ".:?"
             else ".:"
      val = case () of
        () -- | (_schemaType s == Just OpenApiInteger) && (_schemaFormat s == Just "unix-time") ->
               -- par $ (var "fromSeconds") @@ (op (var "o") ".:" (string $ T.unpack fieldName))
           | otherwise -> (string $ T.unpack fieldName)
    in op' (var "o") oper val
mkJsonField _ requiredFields (fieldName, (Ref r)) =
  let oper = if ((not $ null requiredFields)  && (not $ fieldName `elem` requiredFields))
             then ".:?"
             else ".:"
  in
        op (var "o") oper (string $ T.unpack fieldName)


-- create newtype, FromJSON and ExpandsTo for an id wrapped in a newtype
-- FIXME: are all Ids expandable? What about the ones used as parameters in operations -- such as InlineProductParamsId. Though perhaps it doesn't hurt anything.
mkId :: GenStyle -> Text -> [HsDecl']
mkId gs baseName =
  let n = textToPascalName $ baseName <> "_id"
  in  ( newtype' (fromString $ T.unpack n) []
       ( recordCon (fromString $ T.unpack n) [ (textToCamelName $ "un_" <> baseName <> "_id",  field $ var "Text") ]
       ) (if gs == AllDeclarations
           then [ deriving' [ var "Read"
                            , var "Show"
                            , var "Eq"
                            , var "Ord"
                            , var "Data"
                            , var "Typeable"
                            ]
                ]
           else [
                ]
         )
      ) : if gs == AllDeclarations
             then [ instance' (var "FromJSON" @@ (var $ fromString $ T.unpack n))
                    [ funBinds "parseJSON" [ match [ bvar "(Aeson.String x)" ] $
                                             op' (var "pure") "$" ((var $ fromString $ T.unpack n) @@ var "x")
                                           , match [ wildP ] (var "mzero")
                                           ]
                    ]
                  , instance' (var "FromJSON" @@ (var "Expandable" @@ (var $ fromString $ T.unpack n)))
                     [ funBinds "parseJSON" [ match [ bvar "v" ] (op (op (var "ID") "<$>" (var "parseJSON" @@ var "v")) "<|>"
                                                                     (op (var "Expanded") "<$>" (var "parseJSON" @@ var "v")))
                                            ]
                     ]
                  , typeInstance' ("ExpandsTo "<> T.unpack (textToPascalName (baseName <> "_id"))) hsOuterImplicit [] Prefix (var $ fromString $ T.unpack $ textToPascalName baseName)
                  , instance' (var "ToStripeParam" @@ (var $ fromString $ T.unpack n))
                      [ funBinds "toStripeParam" [ match [ conP (fromString $ T.unpack n) [ bvar "t" ] ]
                                                               ( var ":" @@ (tuple [string $ T.unpack baseName
                                                                                   , var "encodeUtf8" @@ var "t"
                                                                                   ]) )
                                                             ]
                      , funBinds "toStripeParamName" [ match [ wildP ] (string $ T.unpack n) ]
                      ]

                  ] ++
                  [ standaloneDeriving (var cn @@ (var "Expandable" @@ (var $ fromString $ T.unpack n)) )  | cn <- derivingNames  ]
--                  [ instance' (var cn @@ (var "Expandable" @@ (var $ fromString $ T.unpack n))) [] | cn <- derivingNames  ]
             else [ instance' (var cn @@ (var "Expandable" @@ (var $ fromString $ T.unpack n))) [] | cn <- derivingNames ] ++
                  [ instance' (var "FromJSON" @@ (var $ fromString $ T.unpack n)) []
                  , instance' (var "FromJSON" @@ (var "Expandable" @@ (var $ fromString $ T.unpack n))) []
--                  , instance' (var "FromJSON" @@ (var $ textToPascalName $ baseName)) []
                  ] ++ [ instance' (var cn @@ (var $ fromString $ T.unpack n)) [] | cn <- derivingNames ]
      -- FIXME: this is definitely not the right way to call typeInstance'


-- create type declarations from 'Referenced Param'
mkParam :: Referenced Param -> [HsDecl']
mkParam (Ref r) = []
mkParam (Inline p) =
  [ newtype' (textToPascalName $ _paramName p) []
      (recordCon (textToPascalName $ _paramName p) []) derivingCommon
  ]

mkObject :: GenStyle -> (Text, Schema) -> ([(RdrNameStr, [RdrNameStr])], [HsDecl'], [(Text, RawValBind)])
mkObject gs (objName', schema) =
  let objName = case objName' of
        -- "automatic_tax" ->  "automatic_tax_object" -- why??
        _               -> objName'
  in {- (mkFromJSON objName schema) : -}
      (schemaToTypeDecls gs False SkipToStripeParam objName objName schema)

mkComponents :: OpenApi -> IO ()
mkComponents oa =
  mapM_ mkComponent (InsOrd.toList (_componentsSchemas (_openApiComponents oa)))

breakCycle :: String -> RdrNameStr -> Bool
{-
breakCycle "File" "FileLink" = True
breakCycle "Price" "Product" = True
breakCycle "Account" "ExternalAccount" = True
breakCycle _ "PaymentMethod" = True
breakCycle "Customer" "TaxId" = True
breakCycle "Customer" "Discount" = True
-- breakCycle "Customer" "PaymentSource" = True
breakCycle "Customer" "InvoiceSettingCustomerSetting" = True
breakCycle "Customer" "Subscription" = True
-- breakCycle "Charge" "PaymentSource" = True
-}
breakCycle _        "Component.Product" = True
breakCycle _        "Component.ApiErrors" = True
--breakCycle _        "PaymentSource" = True
breakCycle _        "Component.FileLink" = True
breakCycle _        "Component.ExternalAccount" = True
--breakCycle _        "PaymentMethod" = True
breakCycle _        "Component.TaxId" = True
breakCycle _        "Component.Discount" = True
breakCycle _        "Component.PaymentSource" = True
breakCycle _        "Component.InvoiceSettingCustomerSetting" = True
breakCycle _        "Component.Subscription" = True
breakCycle _        "Component.Charge" = True
breakCycle _        "Component.Transfer" = True
breakCycle _        "Component.TransferReversal" = True
breakCycle _        "Component.SetupAttempt" = True
breakCycle _        "Component.PaymentIntent" = True
breakCycle _        "Component.Account" = True
breakCycle _        "Component.ApplicationFee" = True
breakCycle _        "Component.Quote" = True
breakCycle _        "Component.BalanceTransaction" = True
breakCycle _        "Component.Invoice" = True
breakCycle _        "Component.IssuingTransaction" = True
breakCycle _        "Component.TreasuryTransaction" = True
breakCycle _        "Component.CustomerBalanceTransaction" = True
-- breakCycle _        "BankAccount" = True


{-
breakCycle "BankAccount" "Account" = True
breakCycle "Card" "Account" = True
breakCycle "PaymentSource" "Account" = True
breakCycle "Subscription" "Account" = True
breakCycle _ "Account" = True
-}
breakCycle _ _ = False

sourceImport a b = if breakCycle a b then source else id
skipImport a b = if breakCycle a b then Just else const Nothing


-- turn each component into a separate Haskell module
mkComponent :: (Text, Schema) -> IO ()
mkComponent component@(name, schema) =
  do let pname :: String
         pname = T.unpack $ textToPascalName name
         extensions = [ DataKinds
                      , DeriveDataTypeable
                      , FlexibleContexts
                      , FlexibleInstances
                      , OverlappingInstances
                      , OverloadedStrings
                      , RecordWildCards
                      , StandaloneDeriving
                      , TypeFamilies
                      , UndecidableInstances
                      ]
         staticImports =
           [ import' "Control.Applicative" `exposing` [ var "pure", var "(<$>)", var "(<*>)", var "(<|>)" ]
           , import' "Control.Monad" `exposing` [ var "mzero" ]
           , import' "Data.Aeson" `exposing` [ thingWith "FromJSON" [ "parseJSON" ]
                                             , thingAll "ToJSON"
                                             , thingWith "Value" [ "String", "Object", "Bool" ]
                                             , var "Object"
                                             , var "(.:)"
                                             , var "(.:?)"
--                                             , var "Object"
                                             ]
           , import' "Data.Aeson.Types" `exposing` [ var "typeMismatch"
                                                   ]
           , qualified' $ import' "Data.Aeson" `as'` "Aeson"
           , import' "Data.Data"  `exposing` [ var "Data", var "Typeable" ]
           , qualified' $ import' "Data.HashMap.Strict" `as'` "H"
           , import' "Data.Map"   `exposing` [ var "Map" ]
           , import' "Data.Ratio" `exposing` [ var "(%)" ]
           , import' "Data.Text"  `exposing` [ var "Text", var "unpack" ]
           , import' "Data.Text.Encoding" `exposing` [ var "encodeUtf8" ]
           , import' "Data.Time"  `exposing` [ var "UTCTime" ]
--           , import' "Numeric"  `exposing` [ var "fromRat" , var "showFFLoat" ]
           , import' "Text.Read"  `exposing` [ var "lexP", var "pfail" ]
           , qualified' $ import' "Text.Read" `as'` "R"
           , import' "Web.Stripe.OneOf" `exposing` [ thingAll "OneOf" ]
           , import' "Web.Stripe.StripeRequest" `exposing`
                       [ thingAll "ToStripeParam"
                       ]
           , import' "Web.Stripe.Types" `exposing` [ thingAll "Expandable"
                                                   , thingAll "StripeList"
                                                   , thingAll "Lines"
                                                   , thingWith "LineItems" []
                                                   , thingWith "Metadata" []
                                                   , var "ExpandsTo"
                                                   , var "Amount"
                                                   , var "Currency"
                                                   , var "UseStripeSdk"
                                                   , var "Status"
                                                   ]
           , import' "Web.Stripe.Util"  `exposing` [ var "fromSeconds" ]
           ]
         exports = Nothing
         (objectImports', objectDecls, toStripeParamBuilder) = mkObject AllDeclarations component
         objectImports = map (\(n, things) -> sourceImport pname n $
                               import' (fromString $ "Web.Stripe." {- Component." -}  <> (rdrNameStrToString n))
                                    `exposing` [ thingWith thing [] | thing <- things ] ) (filter (\(n, _) -> (n /= (textToPascalName name))) objectImports')
         decls = (if name == "customer"
                   -- this is a hack. Not sure why GHC can not find the instance that already exists in PaymentSource
                   then [ typeInstance' "ExpandsTo PaymentSourceId" hsOuterImplicit [] Prefix (var "PaymentSource") ]
                   else []) ++
                 objectDecls ++
--                 concatMap (mkId AllDeclarations) (findIds' component) ++
--                 mkEnums AllDeclarations name (findEnums' component Map.empty) ++

                 []
         modul = module' (Just $ fromString ("Web.Stripe.Component." <> pname)) exports (staticImports ++ objectImports) decls

     formatted <- showModule ("Web/Stripe/Component/" <> pname) extensions modul True
     createDirectoryIfMissing True "_generated/src/Web/Stripe/Component/"
     T.writeFile ("_generated/src/Web/Stripe/Component/" <> pname <> ".hs") formatted
     mkHsBoot component
     pure ()

mkHsBoot :: (Text, Schema) -> IO ()
mkHsBoot component@(name, schema)
  | name `elem` ["charge", "file_link", "external_account", "payment_method", "tax_id", "discount", "payment_source", "invoice_setting_customer_setting", "subscription", "transfer", "api_errors", "setup_attempt", "payment_intent", "transfer_reversal", "account", "application_fee", "quote", "balance_transaction", "invoice", "issuing.transaction", "product", "treasury.transaction", "customer_balance_transaction"] =
  do let extensions = [ DataKinds
                      , DeriveDataTypeable
                      , FlexibleContexts
                      , FlexibleInstances
                      , OverlappingInstances
                      , OverloadedStrings
                      , RecordWildCards
                      , StandaloneDeriving
                      , TypeFamilies
                      , UndecidableInstances
                      ]
         staticImports =
           [ import' "Control.Applicative" `exposing` [ var "pure", var "(<$>)", var "(<*>)", var "(<|>)" ]
           , import' "Control.Monad" `exposing` [ var "mzero" ]
           , import' "Data.Aeson" `exposing` [ thingWith "FromJSON" [ "parseJSON" ]
                                             , thingAll "ToJSON"
                                             , thingWith "Value" [ "String", "Object", "Bool" ]
                                             , var "Object"
                                             , var "(.:)"
                                             , var "(.:?)"
--                                             , var "Object"
                                             ]
           , import' "Data.Aeson.Types" `exposing` [ var "typeMismatch"
                                                   ]
           , import' "Data.Data"  `exposing` [ var "Data", var "Typeable" ]
           , qualified' $ import' "Data.HashMap.Strict" `as'` "H"
           , import' "Data.Map"   `exposing` [ var "Map" ]
           , import' "Data.Ratio" `exposing` [ var "(%)" ]
           , import' "Data.Text"  `exposing` [ var "Text", var "unpack" ]
           , import' "Data.Time"  `exposing` [ var "UTCTime" ]
--           , import' "Numeric"  `exposing` [ var "fromRat" , var "showFFLoat" ]
           , import' "Text.Read"  `exposing` [ var "lexP", var "pfail" ]
           , qualified' $ import' "Text.Read" `as'` "R"
           , import' "Web.Stripe.OneOf" `exposing` [ thingAll "OneOf" ]
           , import' "Web.Stripe.Types" `exposing` [ thingAll "Expandable"
                                                   , thingAll "StripeList"
                                                   , thingAll "Lines"
                                                   , var "ExpandsTo"
                                                   , var "Amount"
                                                   , var "Currency"
                                                   , var "UseStripeSdk"
                                                   , var "Status"
                                                   ]
           , import' "Web.Stripe.Util"  `exposing` [ var "fromSeconds" ]
           ]
         exports = Nothing
         (objectImports', objectDecls, toStripeParamBuilder) = mkObject HsBoot component
         objectImports = [] -- mapMaybe (\(n, things) -> skipImport pname n $ import' (fromString $ "Web.Stripe." {- Component." -}  <> (rdrNameStrToString n))  `exposing` [ thingWith n []]) objectImports'
         decls = [ -- ExpandsTo
                 ] ++
                 objectDecls ++
                 concatMap (mkId HsBoot) (findIds' component) ++
--                 mkEnums (findEnums' component Map.empty) ++

                 []
         pname :: String
         pname = T.unpack $ textToPascalName name
         modul = module' (Just $ fromString ("Web.Stripe.Component." <> pname)) exports (staticImports ++ objectImports) decls

     formatted <- showModule ("Web/Stripe/Component/" <> pname) extensions modul True
     createDirectoryIfMissing True "_generated/src/Web/Stripe/Component/"
     T.writeFile ("_generated/src/Web/Stripe/Component/" <> pname <> ".hs-boot") formatted
     pure ()
mkHsBoot component@(name, schema) = pure ()
{-
showAmount
  :: Currency -- ^ `Currency`
  -> Int      -- ^ `Amount`
  -> String
showAmount cur amt =
  case cur of
   USD -> "$" ++ show2places (currencyDivisor cur amt)
   _   -> show2places (currencyDivisor cur amt) ++ " " ++ show cur
  where
    show2places v = showFFloat (Just 2) v ""
-}

{-
------------------------------------------------------------------------------
-- currency division funtion accounting for zero currencies
--
-- https:\/\/support.stripe.com\/questions\/which-zero-decimal-currencies-does-stripe-support
currencyDivisor
    :: Currency -- ^ `Currency`
    -> (Int -> Float) -- ^ function to convert amount to a float
currencyDivisor cur =
  case cur of
    BIF -> zeroCurrency
    CLP -> zeroCurrency
    DJF -> zeroCurrency
    GNF -> zeroCurrency
    JPY -> zeroCurrency
    KMF -> zeroCurrency
    KRW -> zeroCurrency
    MGA -> zeroCurrency
    PYG -> zeroCurrency
    RWF -> zeroCurrency
    VND -> zeroCurrency
    VUV -> zeroCurrency
    XAF -> zeroCurrency
    XOF -> zeroCurrency
    XPF -> zeroCurrency
    EUR -> hundred
    USD -> hundred
    CHF -> hundred
    _   -> error $ "please submit a patch to currencyDivisor for this currency: " ++ show cur
  where
    zeroCurrency = fromIntegral
    hundred v    = fromRat $ fromIntegral v % (100 :: Integer)

-}
showAmount :: [HsDecl']
showAmount =
  [ typeSig "showAmount" $ var "Currency" --> var "Int" --> var "String"
  , funBind "showAmount" $ matchGRHSs [ bvar "cur", bvar "amt" ] $
      (rhs (case' (var "cur")
        [ match [ conP "USD" [] ] ( op (string "$") "++" (var "show2places" @@ (var "currencyDivisor" @@ var "cur" @@ var "amt")))
        , match [ wildP ] (op (var "show2places" @@ (var "currencyDivisor" @@ var "cur" @@ var "amt" )) "++" (op (string " ") "++" (var "show" @@ var "cur")))
        ])  `where'`
     [ funBind "show2places" $ match [ bvar "v" ] $ var "showFFloat" @@ (var "Just" @@ var "2") @@ (var "v") @@ (string "") ])
  , typeSig "currencyDivisor" $ var "Currency" --> (var "Int" --> var "Float")
  , funBind "currencyDivisor" $ matchGRHSs [ bvar "cur" ] $
      (rhs (case' (var "cur")
             [ -- match [ conP "BIF" [] ] (var "zeroCurrency")
               match [ conP "USD" [] ] (var "hundred")
             ]) `where'`
        [ funBind "hundred" $ matchGRHSs [ bvar "v"] $ (rhs (op (var "fromRat") "$" (op (var "fromIntegral" @@ var "v") "%" (var "100")))) ])
  ]
-- create Web.Stripe.Types
{-
mkTypes :: OpenApi -> IO ()
mkTypes oa =
  do let extensions = [ DataKinds
                      , DeriveDataTypeable
                      , FlexibleContexts
                      , FlexibleInstances
                      , OverlappingInstances
                      , OverloadedStrings
                      , RecordWildCards
                      , StandaloneDeriving
                      , TypeFamilies
                      , UndecidableInstances
                      ]
         imports =
           [ import' "Control.Applicative" `exposing` [ var "pure", var "(<$>)", var "(<*>)", var "(<|>)" ]
           , import' "Control.Monad" `exposing` [ var "mzero" ]
           , import' "Data.Aeson" `exposing` [ thingWith "FromJSON" [ "parseJSON" ]
                                             , thingAll "ToJSON"
                                             , thingAll "Value" -- [ "String", "Object", "Bool" ]
                                             , var "Object"
                                             , var "(.:)"
                                             , var "(.:?)"
--                                             , var "Object"
                                             ]
           , import' "Data.Aeson.Types" `exposing` [ var "typeMismatch"
                                                   ]
           , import' "Data.Data"  `exposing` [ var "Data", var "Typeable" ]
           , qualified' $ import' "Data.HashMap.Strict" `as'` "H"
           , import' "Data.Map"   `exposing` [ var "Map" ]
           , import' "Data.Ratio" `exposing` [ var "(%)" ]
           , import' "Data.Text"  `exposing` [ var "Text", var "unpack" ]
           , import' "Data.Time"  `exposing` [ var "UTCTime" ]
           , import' "Numeric"  `exposing` [ var "fromRat" , var "showFFloat" ]
           , import' "Text.Read"  `exposing` [ var "lexP", var "pfail" ]
           , qualified' $ import' "Text.Read" `as'` "R"
           , import' "Web.Stripe.OneOf" `exposing` [ thingAll "OneOf" ]
           , import' "Web.Stripe.Util"  `exposing` [ var "fromSeconds" ]
           ]
         exports = Nothing
-- charge         charge = (componentSchemaByName oa "charge")
         cs = _componentsSchemas (_openApiComponents oa)
         decls = [ standaloneDeriving (var "Ord" @@ var "Value")

                 , -- ExpandsTo
                   typeFamily' OpenTypeFamily TopLevel "ExpandsTo" [bvar "id"] Prefix (KindSig NoExtField (hsStarTy False))
--                 , tyFamInst "ExpandsTo" [var "AccountId"] (var "Account")
                 -- fixme -- fake types
                 , data' "LineItems" []  [ prefixCon "LineItems" [] ] derivingCommon
                 , instance' (var "FromJSON" @@ var "LineItems")
                      [ funBinds "parseJSON" [ match [ bvar "v" ] ( var "pure" @@ var "undefined" )] ]
--                 , data' "FixMe4b" []  [ prefixCon "FixMe4b" [] ] derivingCommon
--                 , data' "FixMe4bId" []  [ prefixCon "FixMe4bId" [] ] derivingCommon
--                 , typeInstance' "ExpandsTo FixMe4bId"  hsOuterImplicit [] Prefix (var "FixMe4bId")
                 , data' "UseStripeSdk" []  [ prefixCon "UseStripeSdk" [] ] derivingCommon
                 , instance' (var "FromJSON" @@ var "UseStripeSdk")
                     -- FIXME: UseStripeSdk is supported to be a hash
                     [ funBinds "parseJSON" [ match [bvar "(Data.Aeson.Object o)"]  (var "pure" @@ var "UseStripeSdk") ] --  (var "pure" @@ (var "UseStripeSdk" @@ var "o"))]
                     ]
--                 , instance' (var "FromJSON" @@ var "StripeType") [ funBinds "parseJSON" [ match []  (var "undefined")] ]
--                 , data' "Refunds" []  [ prefixCon "Refunds" [] ] derivingCommon
                 , data' "Expandable" [ bvar "id" ] [ prefixCon "ID" [ field $ var "id" ]
                                                    , prefixCon "Expanded"  [field $ var "ExpandsTo" @@ var "id"]
                                                    ] [ deriving' [ var "Typeable" ]]
                 , typeInstance' "ExpandsTo (OneOf [a,b])" hsOuterImplicit [] Prefix (var "OneOf" @@ (listPromotedTy [ var "ExpandsTo" @@  var "a", var "ExpandsTo" @@ var "b"]))
                 , typeInstance' "ExpandsTo (OneOf [a,b,c])" hsOuterImplicit [] Prefix (var "OneOf" @@ (listPromotedTy [ var "ExpandsTo" @@  var "a", var "ExpandsTo" @@ var "b", var "ExpandsTo" @@ var "c"]))

                 , standaloneDeriving $ [ var "Data" @@ var "id"
                                        , var "Data" @@ (var "ExpandsTo" @@ var "id")
                                        ] ==> (var "Data" @@ (var "Expandable" @@ var "id"))
                 , standaloneDeriving $ [ var "Show" @@ var "id"
                                        , var "Show" @@ (var "ExpandsTo" @@ var "id")
                                        ] ==> (var "Show" @@ (var "Expandable" @@ var "id"))
                 , standaloneDeriving $ [ var "Read" @@ var "id"
                                        , var "Read" @@ (var "ExpandsTo" @@ var "id")
                                        ] ==> (var "Read" @@ (var "Expandable" @@ var "id"))
                 , standaloneDeriving $ [ var "Eq" @@ var "id"
                                        , var "Eq" @@ (var "ExpandsTo" @@ var "id")
                                        ] ==> (var "Eq" @@ (var "Expandable" @@ var "id"))
                 , standaloneDeriving $ [ var "Ord" @@ var "id"
                                        , var "Ord" @@ (var "ExpandsTo" @@ var "id")
                                        ] ==> (var "Ord" @@ (var "Expandable" @@ var "id"))
                 ] ++
--                 [ standaloneDeriving $ (var cls @@ (var "Expandable" @@ (var "OneOf" @@ listPromotedTy []))) | cls <- [ "Eq", "Data", "Ord", "Read", "Show"] ] ++
--                 [ standaloneDeriving $ [ var cls @@ var "a", var cls  @@ (var "ExpandsTo" @@ (var "OneOf" @@ var "a"))] ==> (var cls @@ (var "Expandable" @@ (var "OneOf" @@ var "a" ))) | cls <- [ "Eq", "Data", "Ord", "Read", "Show"] ] ++
--                 [ standaloneDeriving $  var cls @@ (var "Expandable" @@ (var "OneOf" @@ (op (var "a") ":" (var "as") ))) | cls <- [ "Eq", "Data", "Ord", "Read", "Show"] ] ++
{-                 [ instance' (var cls @@ (var "Expandable" @@ (var "OneOf" @@ (op (var "a") ":" (var "as") )))) []
                      | cls <- [ "Eq", "Data", "Ord", "Read", "Show"
                               ]
                      ] ++-}
                 [ instance' ([var "Typeable" @@ var "a" ] ==> var cls @@ (var "Expandable" @@ (var "OneOf" @@  var "a"))) []
                      | cls <- [ "Eq", "Data", "Ord", "Read", "Show"
                               ]
                      ] ++
                 [ instance' ([ var "FromJSON" @@ var "id"
                              , var "FromJSON" @@ (var "ExpandsTo" @@ var "id")
                              ] ==> var "FromJSON" @@ (var "Expandable" @@ var "id"))
                              [ funBinds "parseJSON" [ match [bvar "v"] $
                                                       op (op  (var "ID") "<$>" (var "parseJSON" @@ var "v"))
                                                          "<|>"
                                                          (op (var "Expanded") "<$>" (var "parseJSON" @@ var "v"))
                                                     ]
                              ]
                 , instance' (var "FromJSON" @@ (var "Expandable" @@ (var "OneOf" @@ var "rs")))
                     [ funBinds "parseJSON" [ match [ wildP ] $
                                                var "error" @@ string "FromJSON (Expandable (OneOf rs)) not implemented yet"
                                             ]
                     ]
                 , data' "TimeRange" [ bvar "a"]
                    [ recordCon "TimeRange"
                        [ ("gt" , field $ var "Maybe" @@ var "a")
                        , ("gte", field $ var "Maybe" @@ var "a")
                        , ("lt" , field $ var "Maybe" @@ var "a")
                        , ("lte", field $ var "Maybe" @@ var "a")
                        ]
                    ] [ deriving' [ var "Read"
                                  , var "Show"
                                  , var "Eq"
                                  , var "Ord"
                                  , var "Data"
                                  , var "Typeable"
                                  ]
                      ]
                 , data' "StripeList" [ bvar "a" ]
                    [ recordCon "StripeList"
                       [ ("list"      , field $ listTy (var "a"))
                       , ("stripeUrl" , field $ var "Text")
                       , ("object"    , field $ var "Text")
                       , ("totalCount", field $ var "Maybe" @@ var "Int")
                       , ("hasMore"   , field $ var "Bool")
                       ]
                    ] derivingCommon
                 , instance' ([var "FromJSON" @@ var "a"] ==> (var "FromJSON" @@ (var "StripeList" @@ var "a")))
                     [ funBinds "parseJSON" [ match [bvar "(Data.Aeson.Object o)"] $
                                              op' (var "StripeList") "<$>" $ addAp [ op (var "o") ".:"  (string "data")
                                                                                   , op (var "o") ".:"  (string "url")
                                                                                   , op (var "o") ".:"  (string "object")
                                                                                   , op (var "o") ".:?" (string "total_count")
                                                                                   , op (var "o") ".:"  (string "has_more")
                                                                                   ]
                                            ]
--                                              (var "StripeList") @@ op' (var $ textToPascalName name) "<$>" $ addAp $ map (mkJsonField name) $ properties
                     ]
                 , newtype' "ExpandParams" [] (recordCon "ExpandParams" [ ( fromString "getExpandParams", field $ listTy (var "Text"))])  derivingCommon
                 , newtype' "EndingBefore" [ bvar "a" ] (recordCon "EndingBefore" [ ( fromString "getEndingBefore", field $ var "a") ])  derivingCommon
                 , newtype' "StartingAfter" [ bvar "a" ] (recordCon "StartingAfter" [ ( fromString "getStartingAfter", field $ var "a") ])  derivingCommon
                 , newtype' "Limit" [ ] (recordCon "Limit" [ ( fromString "getLimit", field $ var "Int") ])  derivingCommon
                 , newtype' "Metadata" [ ] (recordCon "Metadata" [ ( fromString "unMetadata", field $ listTy $ tuple [ var "Text", var "Text" ])])  derivingCommon
                 , data' "UpTo" [] [ prefixCon "Inf" []
                                   , prefixCon "UpTo" [ strict $ field $ var "Integer" ]
                                   ] derivingCommon
                 , instance' (var "FromJSON" @@ var "UpTo")
                      [ funBinds "parseJSON" [ match [ bvar "(Data.Aeson.String \"inf\")"] ( var "pure" @@ var "Inf" )
                                             , match [ bvar "v"] ( op (var "UpTo") "<$>" (var "parseJSON" @@ var "v"))
                                             ]
                      ]
                 , instance' (var "FromJSON" @@ var "Metadata")
                      [ funBinds "parseJSON" [ match [ bvar "v" ] (op (var "Metadata") "<$>" (var "parseJSON" @@ var "v") ) ]
                      ]

                 , data' "NowOrLater" [] [ prefixCon "Now" []
                                         , prefixCon "Later" [ strict $ field $ var "UTCTime" ]
                                         ] derivingCommon
                 , data' "Lines" [ bvar "a" ]
                    [ recordCon "Lines"
                       [ ("linesData"   , field $ listTy (var "a"))
                       , ("linesUrl"    , field $ var "Text")
                       , ("linesObject" , field $ var "Text") -- the spec seems to indicate this will always be the string 'lines'
                       , ("linesHasMore", field $ var "Bool")
                       ]
                    ]  derivingCommon
                 , instance' ([var "FromJSON" @@ var "a"] ==> var "FromJSON" @@ (var "Lines" @@ var "a"))
                     [ funBinds "parseJSON" [ match [bvar "(Data.Aeson.Object o)"] $
                                              op' (var "Lines") "<$>" $ addAp [ op (var "o") ".:"  (string "data")
                                                                              , op (var "o") ".:"  (string "url")
                                                                              , op (var "o") ".:"  (string "object")
                                                                              , op (var "o") ".:"  (string "has_more")
                                                                              ]
                                            ]
--                                              (var "StripeList") @@ op' (var $ textToPascalName name) "<$>" $ addAp $ map (mkJsonField name) $ properties
                     ]
                 , data' "Emptyable" [ bvar "a" ]
                    [ prefixCon "Full"  [ strict $ field $ var "a" ]
                    , prefixCon "Empty" []
                    ] derivingCommon
                 , data' "Status" []
                    [ prefixCon "Active" []
                    , prefixCon "Inactive" []
                    , prefixCon "Pending" []
                    ] derivingCommon
                 , instance' (var "FromJSON" @@ var "Status")
                     [ funBinds "parseJSON" [ match [ conP "String" [ bvar "c" ] ] $
                                                case' (var "c")
                                                 [ match [ string "active" ] (var "pure" @@ var "Active")
                                                 , match [ string "inactive" ] (var "pure" @@ var "Inactive")
                                                 , match [ string "pending" ] (var "pure" @@ var "Pending")
                                                 ]
                                            ]
                     ]
{-
                 , type' "PaymentSourceId" [] (var "OneOf" @@ listPromotedTy [ var "AccountId"
                                                                             ] )
                 , type' "BalanceTransactionSourceId" [] (var "OneOf" @@ listPromotedTy
                                                                             [ var "ApplicationFeeId"
                                                                             ] )
-}
                 ] ++  map mkTimeNewtype timeNewtypes ++
                 [ data' "Currency" []
                    [ prefixCon "USD" [] -- FIXME, calculate entire list
                    ] [ deriving' [ var "Read"
                                  , var "Show"
                                  , var "Eq"
                                  , var "Ord"
                                  , var "Data"
                                  , var "Typeable"
                                  ]
                      ]
                 , instance' (var "FromJSON" @@ var "Currency")
                     [ funBinds "parseJSON" [ match [ conP "String" [ string "USD" ] ] ( var "pure" @@ var "USD" )
                                            , match [ wildP ]                          ( var "pure" @@ var "USD" )
                                            ]
                     ] -- FIXME: add all currencies

                 , newtype' "Amount" [] (recordCon "Amount" [ ("getAmount", field $ var "Int") ]) derivingCommon
                 , instance' (var "FromJSON" @@ var "Amount") [ funBinds "parseJSON" [ match [ bvar "a" ]  (op (var "Amount") "<$>" (var "parseJSON" @@ (var "a")) )] ]
                   -- emptyTimeRange
                 , typeSig "emptyTimeRange" $ var "TimeRange" @@ var "a"
                 , funBind "emptyTimeRange" $ match [] (var "TimeRange" @@ var "Nothing" @@ var "Nothing" @@ var "Nothing" @@ var "Nothing" )
                 ] ++ showAmount ++
--                 mkEnums (findEnums oa) ++
--                 concatMap mkId (findIds oa) ++
--                 concatMap mkObject (InsOrd.toList cs) ++
--                 concatMap mkParam (findParams oa) ++
                 []
--                 concatMap (uncurry (schemaToTypeDecls "foo")) ([ (t, s) | (t, Inline s) <- findRequestBodyProperties oa ])

         modul = module' (Just "Web.Stripe.Types") exports imports decls

     formatted <- showModule "Web/Stripe/Types.hs" extensions modul True

{-
     let decls = schemaToTypeDecls "charge" "charge" charge
     ch <- runGhc (Just libdir) $
            do dflags <- getDynFlags
               pure $ showPpr dflags (head decls)
     print $ ppSchema charge
     print $ sort $ map fst $ InsOrd.toList $ _schemaProperties charge
     putStr $ ch
-}
--     T.putStr formatted
     createDirectoryIfMissing True "_generated/src/Web/Stripe"
     T.writeFile "_generated/src/Web/Stripe/Types.hs" formatted
     pure ()
       where
         mkTimeNewtype n = newtype' n []
                    ( prefixCon n [ field $ var "UTCTime" ]
                    ) [ deriving' [ var "Read"
                                  , var "Show"
                                  , var "Eq"
                                  , var "Ord"
                                  , var "Data"
                                  , var "Typeable"
                                  ]
                      ]
-}
showGhc a =
  runGhc (Just libdir) $
    do dflags <- getDynFlags
       pure $ showPpr dflags a

timeNewtypes = [ "AvailableOn", {- "Created", -} "Date" ]

findIds :: OpenApi -> [Text]
findIds oa =
  let cs = _componentsSchemas (_openApiComponents oa)
  in (concatMap findIds' $ InsOrd.toList cs)

findIds' :: (Text, Schema) -> [Text]
findIds' (obj, s) =
  case InsOrd.lookup "id" (_schemaProperties s) of
    Nothing -> []
    (Just _) -> [ obj ]

{-
-- FIMXE: make sure that types with the same name are actually compatible
findRequestBodyProperties :: OpenApi -> [(Text, Referenced Schema)]
findRequestBodyProperties oa =
  nubBy ((==) `on` fst) $ concatMap (findPropertiesInPathItems . snd) $ (InsOrd.toList $ _openApiPaths oa)

findPropertiesInPathItems :: PathItem -> [(Text, Referenced Schema)]
findPropertiesInPathItems pi =
  findPropertiesInOperation (_pathItemGet pi) <>
  findPropertiesInOperation (_pathItemPut pi) <>
  findPropertiesInOperation (_pathItemPost pi) <>
  findPropertiesInOperation (_pathItemDelete pi)

findPropertiesInOperation :: Maybe Operation -> [(Text, Referenced Schema)]
findPropertiesInOperation Nothing = []
findPropertiesInOperation (Just op) =
  case _operationRequestBody op of
    Nothing -> []
    (Just (Ref _)) -> []
    (Just (Inline rb)) -> findPropertiesInRequestBody rb

findPropertiesInRequestBody :: RequestBody -> [(Text, Referenced Schema)]
findPropertiesInRequestBody rb =
  case InsOrd.lookup "application/x-www-form-urlencoded" $ _requestBodyContent rb of
    Nothing -> []
    (Just mto) ->
      case _mediaTypeObjectSchema mto of
        Nothing -> []
        (Just (Ref _)) -> []
        (Just (Inline s)) ->
          InsOrd.toList (_schemaProperties s)
-}
{-
findParams :: OpenApi -> [Referenced Param]
findParams oa =
  concatMap findParamsInPathItem (InsOrd.toList $ _openApiPaths oa)

findParamsInPathItem :: (FilePath, PathItem) -> [Referenced Param]
findParamsInPathItem (fp, pi) =
  findParamsInOperation (_pathItemGet pi) <>
  findParamsInOperation (_pathItemPut pi) <>
  findParamsInOperation (_pathItemPost pi) <>
  findParamsInOperation (_pathItemDelete pi)

findParamsInOperation :: Maybe Operation -> [Referenced Param]
findParamsInOperation Nothing   = []
findParamsInOperation (Just op) = _operationParameters op
-}
findEnums :: OpenApi -> Map Text (Set Text)
findEnums oa =
    foldr findEnums' Map.empty (InsOrd.toList $ _componentsSchemas (_openApiComponents oa))

findEnums' :: (Text, Schema) -> Map Text (Set Text)  -> Map Text (Set Text)
findEnums' (tyName, schema) enums
  | _schemaType schema == Just OpenApiObject =
      foldr findEnums' enums (mapMaybe inline $ InsOrd.toList $ _schemaProperties schema)
  | _schemaType schema == Just OpenApiArray =
      case _schemaItems schema of
        (Just (OpenApiItemsObject (Inline s))) ->
          findEnums' (tyName, s) enums
        _ -> enums
--      foldr findEnums' enums (mapMaybe inline $ InsOrd.toList $ _schemaProperties schema)
  where
    inline :: (Text, Referenced Schema) -> Maybe (Text, Schema)
    inline (t, Inline s) = Just (t, s)
    inline (t, Ref _) = Nothing
findEnums' (tyName, _schemaEnum -> Just enum) enums =
      Map.insertWith Set.union tyName (Set.fromList $ [ s | (Aeson.String s) <- enum]) enums
{-
  case enum of
    -- if the enum is just these three fields, then we will just use the generic 'Status' enum
    [Aeson.String "active",Aeson.String "inactive",Aeson.String "pending"] ->
      enums
    _ ->
-}

findEnums'  _ enums = enums
--findEnums' (tyName, s) _ = error $ show $ (tyName, ppSchema s)
{-
mkEnums :: GenStyle -> Text -> Map Text (Set Text) -> [HsDecl']
mkEnums gs p (Map.toList -> enums) = concatMap mkEnum $ {- filter (\(t,c) -> not $ "_payments" `T.isSuffixOf` t) -} enums
  where
    mkCon :: Text -> Text -> ConDecl'
    mkCon "network_status" conName =
      prefixCon (textToPascalName ("network_status_" <> conName)) []
    mkCon "unit" conName =
      prefixCon (textToPascalName (conName <> "_unit")) []
    mkCon "country" conName =
      prefixCon (textToPascalName ("country_" <> conName)) []
    mkCon "preferred_language" conName =
      prefixCon (textToPascalName ("prefered_language_" <> conName)) []
    mkCon t@"allowed_countries" conName =
      prefixCon (textToPascalName (t <> "_" <> conName)) []
    mkCon tyName "" =
      prefixCon (textToPascalName (tyName <> "_empty")) []
    mkCon tyName conName
      | conName `elem` ["active", "auto", "automatic", "checking", "savings", "void", "unpaid", "restricted", "under_review", "paid", "redacted", "lost", "expired", "failed", "canceled", "completed", "ip_address", "stolen", "manual", "fraudulent", "duplicate", "if_required", "sporadic", "exempt", "none",  "inactive", "other", "pending", "required", "reverse", "bank_account_restricted", "debit_not_authorized", "insufficient_funds", "requested_by_customer", "abandoned", "in_progress", "not_collecting", "not_supported", "reverse_charge", "accepted","company","individual", "savings", "other", "checking", "restricted", "unpaid", "credit", "requirements_past_due", "match", "mismatch", "not_provided", "account_closed", "account_frozen", "country", "cancel", "unknown", "unrestricted", "always", "customer_exempt", "issuing_authorization", "shipping", "source", "card", "id", "subscription", "customer_id", "string", "tax_id", "instant", "link", "zengin", "us_domestic_wire", "spei", "sepa", "ach", "payment_method", "standard", "blik", "unused", "too_expensive", "too_complex", "switched_service", "missing_features", "low_quality", "customer_service", "verification_method_instant", "us_bank_account", "supported_payment_method_types_link", "supported_networks_zengin", "supported_networks_us_domestic_wire", "supported_networks_spei", "supported_networks_ach", "payment_method", "service_standard", "payment_method_types_blik", "options_used", "options_too_expensive", "options_too_complex", "options_switched_service", "options_missing_features", "options_low_quality", "options_customer_service", "email", "price", "address", "invoice", "promotion_code", "rule", "dispute_evidence", "bank_transfer"] =
          prefixCon (textToPascalName (tyName <> "_" <> conName)) []
      | otherwise =
          prefixCon (textToPascalName conName) []
    mkEnum :: (Text, Set Text) -> [HsDecl']
    mkEnum ("balance", conNms) =
      [ data' (textToPascalName "treasury_balance") [] [ prefixCon (textToPascalName ("type_" <> c)) [] | c <- Set.toList conNms ] (derivingCommon' gs)
      ]
{-
    mkEnum ("type", conNms) =
      [ data' (textToPascalName "stripe_type") [] [ prefixCon (textToPascalName ("type_" <> c)) [] | c <- Set.toList conNms ] derivingCommon
      ]
-}
    mkEnum ("object", conNms) =
      [ data' (textToPascalName "stripe_object") [] [ prefixCon (textToPascalName ("object_" <> c)) [] | c <- Set.toList conNms ] (derivingCommon' gs)
      ]
    mkEnum ("version", conNms) =
      [ data' (textToPascalName "version") [] [ prefixCon (textToPascalName ("V" <> c)) [] | c <- Set.toList conNms ] (derivingCommon' gs)
      ]
    mkEnum (t@"active_features", conNms) =
      [ data' (textToPascalName t) [] [ prefixCon (textToPascalName ("active_features_" <> c)) [] | c <- Set.toList conNms ] (derivingCommon' gs)
      ]
    mkEnum (t@"pending_features", conNms) =
      [ data' (textToPascalName t) [] [ prefixCon (textToPascalName ("pending_features_" <> c)) [] | c <- Set.toList conNms ] (derivingCommon' gs)
      ]
    mkEnum (t@"allowed_categories", conNms) =
      [ data' (textToPascalName t) [] [ prefixCon (textToPascalName (t <> "_" <> c)) [] | c <- Set.toList conNms ] (derivingCommon' gs)
      ]
    mkEnum (t@"blocked_categories", conNms) =
      [ data' (textToPascalName t) [] [ prefixCon (textToPascalName (t <> "_" <> c)) [] | c <- Set.toList conNms ] (derivingCommon' gs)
      ]
    mkEnum (typeNm', conNms)
      | typeNm' == "status" && conNms == Set.fromList [ "active", "inactive", "pending" ] =
          [ type' (textToPascalName $ p <> "_" <> typeNm') [] (var "Status") ]
      | otherwise =
         let typeNm
              | typeNm' == "status" = p <> "_" <> typeNm'
              | typeNm' == "type"   = p <> "_" <> typeNm'
              | otherwise = typeNm'
         in
          (data' (textToPascalName typeNm) [] [ mkCon typeNm c | c <- Set.toList conNms ] (derivingCommon' gs)) :
          if (gs == AllDeclarations)
          then [ instance' (var "FromJSON" @@ (var $ textToPascalName typeNm)) [ funBinds "parseJSON" [ match []  (var "undefined")] ]
               ]
          else []
-}
main :: IO ()
main =
  do oa <- readSpec
--     let e = findEnums oa
--     print $ Map.keys e
     createDirectoryIfMissing True "_generated/src/Web/Stripe"
     copyFile "static/src/Web/Stripe/Client.hs"        "_generated/src/Web/Stripe/Client.hs"
     copyFile "static/src/Web/Stripe/Error.hs"         "_generated/src/Web/Stripe/Error.hs"
     copyFile "static/src/Web/Stripe/StripeRequest.hs" "_generated/src/Web/Stripe/StripeRequest.hs"
     copyFile "static/src/Web/Stripe/OneOf.hs"         "_generated/src/Web/Stripe/OneOf.hs"
     copyFile "static/src/Web/Stripe/Util.hs"          "_generated/src/Web/Stripe/Util.hs"
     copyFile "static/src/Web/Stripe/Types.hs"          "_generated/src/Web/Stripe/Types.hs"
     copyFile "static/stripe-core.cabal"               "_generated/stripe-core.cabal"
     copyFile "static/cabal.project"                   "_generated/cabal.project"
     copyFile "static/shell.nix"                       "_generated/shell.nix"

--     mkTypes oa
     mkComponents oa

     -- Web.Stripe.Account
     mkPaths oa [("/v1/account", Just "AccountId")] (NonEmpty.singleton "Account")
     mkPaths oa [("/v1/accounts", Just "AccountId")] (NonEmpty.singleton "Accounts")
#if 0
--     print [ t  | (t,s) <- findRequestBodyProperties oa ]

     -- Web.Stripe.ApplicationFees
     mkPaths oa [ ("/v1/application_fees",  Just "ApplicationFeeId")
                , ("/v1/application_fees/{id}", Just "ApplicationFeeId")
                ] (NonEmpty.singleton "ApplicationFees")

     -- Web.Stripe.ApplicationFeeRefund
     mkPaths oa [ ("/v1/application_fees/{id}/refunds" , Just "ApplicationFeeId")
                , ("/v1/application_fees/{fee}/refunds/{id}", Just "FeeRefundId")
                ] (NonEmpty.singleton "ApplicationFeesRefund")

     -- Web.Stripe.Balance
     mkPaths oa [ ("/v1/balance" , Nothing)
                ] (NonEmpty.singleton "Balance")
#endif
     -- Web.Stripe.Customers
     mkPaths oa [ ("/v1/customers" , Just "CustomerId")
--                , ("/v1/subscriptions/{subscription_exposed_id}", Just "SubscriptionId")
                ] (NonEmpty.singleton "Customers")

     -- Web.Stripe.Subscriptions
     mkPaths oa [ ("/v1/subscriptions" , Just "SubscriptionId")
--                , ("/v1/subscriptions/{subscription_exposed_id}", Just "SubscriptionId")
                ] (NonEmpty.singleton "Subscriptions")

     -- Web.Stripe.Plans
     mkPaths oa [ ("/v1/plans" , Just "PlanId")
--                , ("/v1/subscriptions/{subscription_exposed_id}", Just "SubscriptionId")
                ] (NonEmpty.singleton "Plans")

     -- Web.Stripe.Plans
     {-
     mkPaths oa [ ("/v1/plans" , Just "PlanId")
--                , ("/v1/plans/{plan}" , Just "PlanId")
                ] ("Billing" :| ["Plans"])

--     print [ _paramName p  | (Inline p) <- findParams oa ]
--     print [ t  | (t,s) <- findRequestBodyProperties oa ]
-}
--     print [ (t, ppReferenced ppSchema s)  | (t, s) <- findRequestBodyProperties oa, t == "trial_period_days" ]
{-     t <- runGhc (Just libdir) $
            do dflags <- getDynFlags
               let decls = [ schemaToTypeDecls "foo" t s   | (t, Inline s) <- findRequestBodyProperties oa, t == "trial_period_days" ]
               pure $ showPpr dflags decls
     putStrLn t
-}
--     mkPath oa "/v1/application_fees/{id}"  "ApplicationFeeId" "ApplicationFees"
{-
     let allPaths = InsOrd.toList (_openApiPaths s)
     mapM_ print (sort $ map fst allPaths)
     print (length allPaths)
     let componentName = "balance_amount"
         (Just comp) = InsOrd.lookup componentName $ _componentsSchemas (_openApiComponents s)

     let cs :: [(Text, Schema)]
         cs = InsOrd.toList (_componentsSchemas (_openApiComponents s))
         decls = concatMap (\(n,s) -> schemaToTypeDecls n s) [(componentName, comp)]
-}
--      print $ ppSchema comp
--     runGhc (Just libdir) $ putPpr $
--       module' (Just $ textToPascalName componentName) Nothing [] decls
     pure ()
{-
  do s <- readSpec
     let ss = subscriptionSchema s
--     print $ map (_schemaTitle . (\(Inline i) -> i) . snd) $ InsOrd.toList $ _schemaProperties ss
     let componentName = "subscription_automatic_tax"
         (Just p) = InsOrd.lookup componentName $ _componentsSchemas (_openApiComponents s)
--     print $ ppSchema p
         cs :: [(Text, Schema)]
         cs = InsOrd.toList (_componentsSchemas (_openApiComponents s))
     let decls = concatMap (\(n,s) -> schemaToTypeDecls n s) cs
     let path = "/v1/customers/{customer}"
         (Just pi) = InsOrd.lookup path (_openApiPaths s)
--         (Just op) = _pathItemGet pi
         (Just op) = _pathItemPost pi
     -- print $ ppOperation $ fromJust $ _pathItemGet pi
     {-
     print $ ppList $ map (ppReferenced ppParam) (_operationParameters $ fromJust $ _pathItemPost pi)
     let paramDecls = map referencedParamToDecl (_operationParameters $ fromJust $ _pathItemPost pi)
         ds = WithHsDocIdentifiers (GeneratedDocString (mkHsDocStringChunk "This is my DocD")) []
         ss :: SrcSpan
         ss = mkGeneralSrcSpan "<strip-api-gen>"
         l :: GenLocated SrcSpan (HsDoc GhcPs)
         l = L ss ds
     let dd = DocD noExtField  (DocCommentNext l)
     -}
     -- print $ ppOperation op
     let opDecls = mkOperation path "POST" op
     runGhc (Just libdir) $ putPpr $
       module' (Just "Subscription") Nothing [] {- decls++ -} opDecls
-}
--     let params = take 1 $ InsOrd.toList $ _componentsCallbacks (_openApiComponents s)
--     print params
--     pp p
--     runGhc (Just libdir) $ putPpr $ schemaToEnumDecl "collection_method" p
     -- runGhc (Just libdir) $ putPpr typesModule
--     runGhc (Just libdir) $ putPpr (DeclDocMap (Map.fromList [("const", mkHsDocString "const doc string")]))
---     printDoc PageMode 120 stdout
     pure ()

-- * Parser stuff from GHC.Parser

-- doc = docDeclDec (DocCommentNext (noLoc (hsDocString (NestedDocString HsDocStringNext (noLoc "this is some documentation.")))))

-- DeclDocMap
-- doc = DocD noExt (DocCommentNext $ mkHsDocString "This is a comment.")

runParser :: ParserOpts -> String -> P a -> ParseResult a
runParser opts str parser = unP parser parseState
    where
      filename = "<interactive>"
      location = mkRealSrcLoc (mkFastString filename) 1 1
      buffer = stringToStringBuffer str
      parseState = initParserState opts buffer location

defDiagOpts =
  DiagOpts EnumSet.empty EnumSet.empty False False Nothing defaultSDocContext

defParserOpts =
  mkParserOpts EnumSet.empty defDiagOpts [] True True True True

t = case  (runParser defParserOpts "foo :: a -- ^ foo\n -> b -> c" parseModule ) of (POk  _ a) -> runGhc (Just libdir) $ putPpr a ; (PFailed st) -> error $ "failed"
t2 = case  (runParser defParserOpts "foo :: a -- ^ foo \n-> b -> c\n" parseStmt) of (POk  _ a) -> runGhc (Just libdir) $ putPpr a ; (PFailed st) -> error $ "failed"


-- *
{-
builtSpan :: SrcSpan
builtSpan = mkGeneralSrcSpan "<ghc-source-gen>"

builtLoc :: e -> Located e
builtLoc = L builtSpan
{-
#if MIN_VERSION_ghc(9,2,0)
type SrcSpanAnn ann = GHC.SrcSpanAnn' (EpAnn ann)
#else
type SrcSpanAnn ann = SrcSpan
#endif
-}

mkLocated :: a -> GenLocated (SrcSpanAnn ann) a
mkLocated = L (toAnn builtSpan)
  where
    toAnn = SrcSpanAnn EpAnnNotUsed

newOrDataType
    :: NewOrData
    -> OccNameStr
    -> [HsTyVarBndr']
    -> [ConDecl']
    -> [HsDerivingClause']
    -> HsDecl'
newOrDataType newOrData name vars conDecls derivs
    = noExt TyClD $ withPlaceHolder $ withPlaceHolder $
        withEpAnnNotUsed DataDecl (typeRdrName $ unqual name)
            (mkQTyVars vars)
            Prefix
            $ noExt HsDataDefn newOrData
                cxt
                Nothing
                Nothing
                (map mkLocated conDecls)
                (toHsDeriving $ map builtLoc derivs)
  where
    cxt = Nothing
    toHsDeriving = id

#if MIN_VERSION_ghc(9,2,0)
type SrcSpanAnn ann = GHC.SrcSpanAnn' (EpAnn ann)
#else
type SrcSpanAnn ann = SrcSpan
#endif


#if MIN_VERSION_ghc(8,10,0)
noExt :: (NoExtField -> a) -> a
noExt = ($ GHC.NoExtField)
#elif MIN_VERSION_ghc(8,6,0)
noExt :: (NoExtField -> a) -> a
noExt = ($ GHC.NoExt)
#else
noExt :: a -> a
noExt = id
#endif


mkQTyVars :: [HsTyVarBndr'] -> LHsQTyVars'
mkQTyVars vars =  withPlaceHolder
                $ noExt (withPlaceHolder HsQTvs)
                $ map mkLocated vars
-}

{-
-- * Simple type declarations
--
-- We need a way to check the parameters declared in different locations in the spec are actually the same, but HsDecl does not implement Eq
data SimpleCon =
  SimpleRecord [Field]
  deriving (Eq, Ord, Show)

data SimpleDecl =
  SimpleData Text [SimpleCon]
  deriving (Eq, Ord, Show)
-}
