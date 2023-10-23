{-# language CPP  #-}
{-# language NoMonomorphismRestriction #-}
{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language TypeFamilies #-}
{-# language DataKinds #-}
{-# language FlexibleInstances #-}
{-# language ViewPatterns #-}
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
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.HashMap.Strict.InsOrd as InsOrd
import Data.HashMap.Strict.InsOrd (InsOrdHashMap)
import Data.Maybe (fromJust, isJust, fromMaybe)
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
textToPascalName = fromString . pascal . (replace '.' '_') . T.unpack

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

referencedSchemaToType :: GenStyle -> Text -> Text -> Referenced Schema -> ([RdrNameStr], HsType', [HsDecl'])
referencedSchemaToType gs objName n (Inline s) = schemaToType gs objName n s
referencedSchemaToType gs objName n (Ref (Reference r)) =
  let imports
        | objName == r = []
        | otherwise = [textToPascalName r]
  in (imports, (var $ textToPascalName r), [])

schemaToType :: GenStyle
             -> Text
             -> Text
             -> Schema
             -> ([RdrNameStr], HsType', [HsDecl'])
schemaToType gs objName n s =
  let (imports, ty, decls) = schemaToType' gs objName n s
  in case _schemaNullable s of
    (Just True) -> (imports, var "Maybe" @@ ty, decls)
    _           -> (imports, ty, decls)

schemaToEnumDecl :: Text    -- ^ objName -- used for disambiguation
                 -> Text    -- ^ enum name
                 -> Schema  -- ^ enum schema
                 -> (HsType', [HsDecl'])
schemaToEnumDecl objNm nm s
  | nm == "version" =
      let (Just vs) =  _schemaEnum s
          cons = [ prefixCon (textToPascalName $ "V" <> c) [] | (Aeson.String c) <- vs ]
          occName  = (textToPascalName (objNm <> "_"<> nm))
          occName' = (textToPascalName (objNm <> "_"<> nm))
      in ((var occName ), [data' occName' [] cons derivingCommon])
  | _schemaType s == Just OpenApiString =
      case _schemaEnum s of
        (Just vs) ->
          let withPrefix t =
                -- FIXME: failure_code is usually a subset of this list
                -- https://stripe.com/docs/error-codes) for a list of codes).
                -- failure_code varies from location to location
                case (nm `elem` ["status", "setup_future_usage", "capture_method"]) of
                  True -> (objNm <> "_" <> t)
                  False -> t
              occNam = textToPascalName $ withPrefix nm
              cons   = [ prefixCon (textToPascalName $ withPrefix c) [] | (Aeson.String c) <- vs ]
          in (var (fromString occNam), [data' (fromString occNam) [] cons derivingCommon])
        Nothing ->
          let typName = textToPascalName nm
              cons     = [ recordCon (fromString $ textToPascalName nm) [ ((fromString $ "un" <> textToPascalName nm)
                                                                          , (strict $ field $ var (fromString "Text"))
                                                                          )
                                                                        ]
                         ]
          in (var (fromString typName) , [data' (fromString typName) [] cons derivingCommon])

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

schemaToType' :: GenStyle
              -> Text
              -> Text
              -> Schema
              -> ([RdrNameStr], HsType', [HsDecl']) -- ^
schemaToType' gs p n s
--  | n == "type" = ([], var "StripeType", [])
  | ((n == "type") && (_schemaType s == Just OpenApiString)) = ([], var "Text", [])
  | n == "type" =  ([], var $ textToPascalName (p <> "_type"), [])
  | (_schemaType s == Just OpenApiInteger) && (_schemaFormat s == Just "unix-time") =
      ([], var "UTCTime", [])
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
--      "currency" -> (var "Currency", [])
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
               ([], (var $ textToPascalName n), mkEnums gs (Map.singleton n (Set.fromList [ s | Aeson.String s <- enums ])))
{-
               [ data' (textToPascalName typeNm) [] [ mkCon typeNm c | c <- Set.toList conNms ] derivingCommon
               , instance' (var "FromJSON" @@ (var $ textToPascalName typeNm)) [ funBinds "parseJSON" [ match []  (var "undefined")] ]
               ]
-}
             _       -> ([], var $ textToPascalName n, []) -- schemaToEnumDecl p n s
  | (_schemaType s == Just OpenApiArray) =
      case _schemaItems s of
        Just (OpenApiItemsObject (Ref (Reference r))) ->
          ([textToPascalName r], var "StripeList" @@ (var $ textToPascalName r), [])
        Just (OpenApiItemsObject (Inline s)) ->
          let name = case _schemaTitle s of
                (Just t) -> t
                Nothing  -> n
              (imports, ty, decls) = schemaToType' gs "FixMe4a" name s
          in (imports, var "StripeList" @@ ty, decls)
        Nothing -> ([], var "FixMeOpenApiItemsObject", [])
  | (_schemaType s == Just OpenApiObject) =
      case (_schemaAdditionalProperties s) of
        (Just (AdditionalPropertiesSchema rSchema)) ->
          let (imports, ty, decls) = referencedSchemaToType gs p n rSchema
          in (imports, var (fromString "Map") @@ var (fromString "Text") @@ ty, decls)
        _ ->
          case n of
            -- handle things which can be expressed via the 'Lines a' type
            "lines" ->
              case InsOrd.lookup "data" (_schemaProperties s) of
                (Just (Inline dataSchema)) ->
                  case _schemaItems dataSchema of
                    (Just (OpenApiItemsObject r)) ->
                      let (imports, ty, decls) = referencedSchemaToType gs p "FixMeLines" r
                      in (imports, var (fromString "Lines") @@ ty, decls)
                    Nothing -> error "Expected 'lines.data' to have an 'items' property"
                Nothing -> error "Expected 'lines' to have a data property"

            _ ->
              let (imports, decls) = schemaToTypeDecls gs p n s
              in (imports, var (fromString $ textToPascalName n), decls)
  | isJust (_schemaAnyOf s) =
      case _schemaAnyOf s of
        (Just [(Inline schema1), (Ref (Reference r))])
          | (_schemaType schema1) == Just OpenApiString ->
              (if p == r then [] else [textToPascalName r], var "Expandable" @@ (var $ fromString $ textToPascalName (r <> "_id")), [])
        _ ->
          case InsOrd.lookup "expansionResources" (_unDefs $ _schemaExtensions s) of
            -- we are dealing with an expandable field
            (Just er) | not (n `elem` ["default_source", "destination"]) -> -- FIXME: the problem here is that the ID can expand to one of several fields
              ([textToPascalName n], var "Expandable" @@ (var $ fromString $ textToPascalName (n <> "_id")), [])
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
                  ([textToPascalName r], (var $ fromString $ textToPascalName r), [])
                o ->
                  let (Just schemas) = _schemaAnyOf s
                      (imports, types, decls) = unzip3 $ map (referencedSchemaToType gs p "FixMe7") schemas
                  in (concat imports, var "OneOf" @@ listPromotedTy types, concat decls)

schemaToType' _ p n s = error $ show $ (n, ppSchema s)
-- schemaToType' _ _ = (var "FixMe", [])

mkNullable :: Schema -> HsType' -> HsType'
mkNullable s ty =
  case _schemaNullable s of
    (Just True) -> var "Maybe" @@ ty
    _           -> ty

textToOccName = fromString . T.unpack

mkRequired :: (Var a, App a) => Bool -> a -> a
mkRequired True a = a
mkRequired False a = var "Maybe" @@ a

-- when do we use _schemaNullable and when do we use _schemaRequired?
schemaToField :: GenStyle -> [ParamName] -> Text -> (Text, Referenced Schema) -> ([RdrNameStr], (OccNameStr, Field), [HsDecl'])
schemaToField gs required objectName (n, Inline s)
  | n == "id" && _schemaType s == Just OpenApiString =
      ([], (fromString $ textToCamelName (objectName <> "_" <> n), strict $ field $ mkRequired (n `elem` required) $ var (fromString $ textToPascalName (objectName <> "_id"))), [])
  | _schemaType s == Just OpenApiInteger && (n `elem` ["amount", "amount_captured", "amount_refunded", "application_fee_amount"]) =
      let ty = case _schemaNullable s of
                 (Just True) -> var "Maybe" @@ var "Amount"
                 _           -> var "Amount"
      in ([], (fromString $ textToCamelName (objectName <> "_" <> n), strict $ field $ ty), [])
-- schemaToField _ (n , Ref _)   = ((textToOccName n, strict $ field $ var "FixMe3"), [])
schemaToField gs required objectName (n , Ref (Reference r))   =
  ([textToPascalName r], (fromString $ textToCamelName(objectName <> "_" <> n), strict $ field $ mkRequired (n `elem` required) $ var $ textToPascalName r ), [])
schemaToField gs required objectName (n, Inline s) =
   let (imports, ty, decls) = schemaToType gs objectName n s
   in (if (n == "amount_tax_display")
        then (trace ("schemaToField" ++ show (ppSchema s)))
        else id) $
     (imports, (fromString $ textToCamelName (objectName <> "_" <> n), strict $ field $ mkRequired (n `elem` required) $ ty) , decls)

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
    _ -> False

isEmptyEnum :: Schema -> Bool
isEmptyEnum schema =
  (_schemaEnum schema == Just [ Aeson.String "" ])


mkNewtypeParam tyName wrappedType =
  let occName   = fromString (textToPascalName tyName)
      conName   = fromString (textToPascalName tyName)
      unConName = fromString ("un" <> textToPascalName tyName)
      con       = recordCon occName [ ( unConName, strict $ field $ wrappedType) ]
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

schemaToTypeDecls :: GenStyle -> Text -> Text -> Schema -> ([RdrNameStr], [HsDecl'])
schemaToTypeDecls gs objName tyName s
  -- types which are manually defined in Types
  | tyName `elem` [ "expand", "metadata" ] = ([], [])
  | tyName `elem` ["lines", "line_items", "use_stripe_sdk", "refunds", "customer_id", "automatic_tax", "currency"] = ([], [])
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
        False -> error "expected on_behalf_of to be a Maybe String. Perhaps the specification has changed?"
        True -> mkNewtypeParam tyName (var "Emptyable" @@ var "AccountId")

  | tyName == "default_tax_rate" =
      case isEmptyableString s of
        False -> error "expected default_tax_rate to be a Maybe String. Perhaps the specification has changed?"
        True -> mkNewtypeParam tyName (var "Emptyable" @@ var "AccountId")

  | _schemaType s == Just OpenApiString =
      ([], []) -- (snd $ schemaToEnumDecl objName tyName s)

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
          | _schemaEnum schema1 == Just [ Aeson.String "now" ] &&
            (_schemaType schema2 == Just OpenApiInteger) && (_schemaFormat schema2 == Just "unix-time")
            -> let occName   = fromString (textToPascalName tyName)
                   conName   = fromString (textToPascalName tyName)
                   unConName = fromString ("un" <> textToPascalName tyName)
                   con       = recordCon occName [ ( unConName, strict $ field $ var "NowOrLater") ]
               in ([], [ newtype' occName [] con (derivingCommon' gs) ])
        _ ->
          case InsOrd.lookup "expansionResources" (_unDefs $ _schemaExtensions s) of
            Nothing ->
              case _schemaAnyOf s of
                (Just [Inline schema1, Inline schema2])
                  | isEmptyEnum schema2 ->
                      schemaToTypeDecls gs "NoObjectName" tyName schema1
                (Just schemas) ->
--                  mkSumType tyName schemas --
                  let (imports, types, decls) = unzip3 $ map (referencedSchemaToType gs objName "FixMe6") schemas
                      occName   = fromString (textToPascalName tyName)
                      conName   = fromString (textToPascalName tyName)
                      unConName = fromString ("un" <> textToPascalName tyName)
                      cons = [ recordCon conName [ (unConName, strict $ field $ (var "OneOf" @@ listPromotedTy types)) ]
                             ]
                  in (concat imports, (data' occName [] cons (derivingCommon' gs) : (if gs == AllDeclarations then [mkFromJSON objName s] else [])))

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
              in (data' occName [] cons derivingCommon : mkFromJSON objName s : [] {- :  concat decls -} )
-}
            (Just er) ->
              error $ show er

  | _schemaType s == Just OpenApiInteger =
      let occName = fromString (textToPascalName $ tyName)
--          (fields, decls) =  unzip $ map (schemaToField (fromMaybe "FixMe2b" (_schemaTitle s))) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
--          (imports, fields, decls) =  unzip3 $ map (schemaToField tyName) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
          con = recordCon occName [ (textToCamelName $ "un_" <> tyName, field $ var "Integer" ) ]
      in ([], [ newtype' occName [] con (derivingCommon' gs) ])
  -- FIXME: should we use a Decimal type instead of Double?
  | _schemaType s == Just OpenApiNumber =
      let occName = fromString (textToPascalName $ tyName)
          con = recordCon occName [ (textToCamelName $ "un_" <> tyName, field $ var "Double" ) ]
      in ([], [ newtype' occName [] con (derivingCommon' gs) ])

  | _schemaType s == Just OpenApiBoolean =
      let occName = fromString (textToPascalName $ tyName)
--          (fields, decls) =  unzip $ map (schemaToField (fromMaybe "FixMe2b" (_schemaTitle s))) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
--          (imports, fields, decls) =  unzip3 $ map (schemaToField tyName) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
          con = recordCon occName [ (textToCamelName $ "un_" <> tyName, field $ var "Bool" ) ]
      in ([], [ newtype' occName [] con (derivingCommon' gs) ])

  | _schemaType s == Just OpenApiArray =
      case _schemaItems s of
        {-
        Just (OpenApiItemsObject (Ref (Reference r))) ->
          ([textToPascalName r], var "StripeList" @@ (var $ textToPascalName r), [])
-}
        Just (OpenApiItemsObject (Inline s))
          | _schemaType s == Just OpenApiString ->
              let occName = fromString (textToPascalName $ tyName)
                  con = recordCon occName [(fromString $ "un" <> textToPascalName tyName, field $ listTy $ var "Text")]
          in ([], (data' occName [] [con] (derivingCommon' gs)) : []) -- : concat decls

        Just (OpenApiItemsObject (Inline s)) ->
          let -- decls' = schemaToTypeDecls "FixMe4a" "FixMe4b" s
              entryTy = case _schemaTitle s of
                          (Just t) -> t
                          Nothing  -> error $ "schemaToTypeDecls - could not find schemaTitle for " ++ show (ppSchema s)
              entryTyName = textToPascalName entryTy
--              (imports, fields, decls) =  unzip $ map (schemaToField (fromMaybe "FixMe2b" (_schemaTitle s))) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
              (entryImports, entryFields, entryDecls) =  unzip3 $ map (schemaToField gs (_schemaRequired s) tyName) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
              entryCon = recordCon entryTyName entryFields
              entryDecl = data' entryTyName [] [entryCon] (derivingCommon' gs)

              occName = fromString (textToPascalName $ tyName)


--              (imports, fields, decls) =  unzip3 $ map (schemaToField tyName) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
--              con = recordCon occName fields
              con = recordCon occName [(fromString $ "un" <> textToPascalName tyName, field $ listTy $ var "a")]
          in (concat entryImports , entryDecl : (data' occName [] [con] (derivingCommon' gs)) : []) -- : concat decls

--          in (listTy $ var (textToPascalName tyName) decls'
{-
          let (imports, ty, decls) = schemaToType' "FixMe4a" "FixMe4b" s
          in (imports, var "StripeList" @@ ty, decls)
        Nothing -> ([], var "schemaToTypeDecls - FixMeOpenApiItemsObject", [])
-}
  | otherwise =
      let name = tyName
          occName = fromString (textToPascalName name)
--          (fields, decls) =  unzip $ map (schemaToField (fromMaybe "FixMe2b" (_schemaTitle s))) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
          (imports, fields, decls) =  unzip3 $ map (schemaToField gs (_schemaRequired s) name) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
          con = recordCon occName fields
      in case gs of
           AllDeclarations -> (concat imports, (data' occName [] [con] (derivingCommon' gs))  : concat decls)
           HsBoot -> ([], data' occName [] [] [] :
                          [instance' (var n @@ var (textToPascalName name)) [] | n <- derivingNames ])
{-
  | otherwise = error $ "schemaToTypeDecls: " ++ show (tyName, ppSchema s)
-}

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

-- FIXME: the list of things which are actually IDs should be computed, not hard coded
mkParamName :: Text -> RdrNameStr
mkParamName p =
  case p of
    "expand" -> fromString "ExpandParams"
    -- things which are actually IDs
    n | n `elem` ["charge", "customer"] -> fromString $ textToPascalName (n <> "_id")
    n        -> fromString $ textToPascalName n

mkStripeHasParam :: OccNameStr -> Maybe Text -> Referenced Param -> (RdrNameStr, HsDecl')
mkStripeHasParam opName mIdName (Inline param) =
  let paramNm = mkParamName $ _paramName param
  in if paramNm `elem` ["StartingAfter", "EndingBefore"]
     then case mIdName of
            Nothing -> error $ "mkStripeHasParam: expect an idName but got Nothing. opName = " ++ show opName ++ " , param = " ++ show (ppParam param)
            (Just idName) -> (textToPascalName idName, instance' (var "StripeHasParam" @@ (var $ UnqualStr opName) @@ (var paramNm @@ (var $ textToPascalName idName))) [])
     else (paramNm, instance' (var "StripeHasParam" @@ (var $ UnqualStr opName) @@ (var $ paramNm)) [])

mkStripeHasParamFromProperty :: OccNameStr -> (Text, (Referenced Schema)) -> [([RdrNameStr], HsDecl', InsOrdHashMap Text [HsDecl'])]
mkStripeHasParamFromProperty opName (pName, (Inline schema)) =
  let pn = mkParamName pName
      inst = instance' (var "StripeHasParam" @@ (var $ UnqualStr opName) @@ (var pn)) []
      (imports, decls) = schemaToTypeDecls AllDeclarations "FixMeHasParamFromProperty1" pName schema
      tys = InsOrd.fromList [(pName, decls)]
  in [(imports, inst, tys)]


mkStripeRequestBodyStripeHasParam :: OccNameStr -> Maybe (Referenced RequestBody) -> ([ParamName], [([RdrNameStr], HsDecl', InsOrdHashMap Text [HsDecl'])])
mkStripeRequestBodyStripeHasParam opName Nothing = ([], [])
mkStripeRequestBodyStripeHasParam opName (Just (Inline rb)) =
  case InsOrd.lookup "application/x-www-form-urlencoded" (_requestBodyContent rb) of
    Nothing -> ([], [])
    (Just mto) ->
      case _mediaTypeObjectSchema mto of
        (Just (Inline schema)) ->
          (_schemaRequired schema, concatMap (mkStripeHasParamFromProperty opName) (InsOrd.toList (_schemaProperties schema )))


responseType :: Response -> ([RdrNameStr], HsType')
responseType resp =
  case InsOrd.lookup "application/json" (_responseContent resp) of
    Nothing -> error $ "responseType: could not find application/json for response " <> show (ppResponse resp)
    (Just mto) ->
      case _mediaTypeObjectSchema mto of
        (Just (Inline schema)) ->
          case InsOrd.lookup "data" (_schemaProperties schema) of
            (Just (Inline dataSchema)) ->
              let (imports, ty, _) = schemaToType AllDeclarations "FixMeResponseType1" "FixMeResponseType" dataSchema
              in (imports, ty)
            Nothing ->
              case _schemaAnyOf schema of
                (Just anyOf) ->
                  ([], var "OneOf" @@ (listPromotedTy $ map (\(Ref (Reference s)) -> var $ textToPascalName s) anyOf))
                Nothing ->
                  do error $ "Could not find schemaProperty named 'data'\n " <> show (ppSchema schema)
        (Just (Ref (Reference s))) ->
          ([textToPascalName s], var (textToPascalName s))

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
mkRequestDecl :: FilePath -> Method -> Maybe Text -> Operation -> [ParamName] -> ([HsDecl'], [RdrNameStr])
mkRequestDecl path method idName oper requiredParams =
  let opName :: OccNameStr
      opName   = textToCamelName $ fromJust $ _operationOperationId oper

      opName' :: RdrNameStr
      opName'  = textToPascalName $ fromJust $ _operationOperationId oper

      request = valBind "request" (var "mkStripeRequest" @@ var (fromString $ show method) @@ var "url" @@ var "params")
      pathTemplate = extractTemplate (T.pack path)
      (patTys, urlE) = mkUrl idName pathTemplate
--      (pats, typs) :: ([Pat'], [HsType'])
      requiredParamTypes = map (var . mkParamName) requiredParams
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
      params  = valBind "params" (var "[]")
  in  ([ typeSig opName ty
       , funBind opName (matchGRHSs pats (rhs (var "request") `where'` [request, url, params]))
       ]
      , [ opName', textToCamelName $ fromJust $ _operationOperationId oper ]
      )

mkOperation :: FilePath   -- ^ path
            -> Method     -- ^ method
            -> Maybe Text -- ^ what type is {id}
            -> Operation
            -> ([RdrNameStr], [HsDecl'], [RdrNameStr], [RdrNameStr]) -- ^ (imports, decls, re-exports, new things to export)
mkOperation path method mIdName op =
  let opName :: OccNameStr
      opName   = textToPascalName $ fromJust $ _operationOperationId op

      -- create a constructorless type for use as the phantom type parameter to StripeRequest
      opIdDecl = data' opName [] [] []

      (requiredParams, decls) = mkStripeRequestBodyStripeHasParam opName (_operationRequestBody op)
      (paramImports, instanceDecls, typeDecls) = unzip3 decls
      typeDecls' :: [HsDecl']
      typeDecls' = concatMap snd $ concatMap InsOrd.toList typeDecls

      reexports =  map (mkParamName . fst) $ concatMap InsOrd.toList typeDecls

      inQuery :: Referenced Param -> Bool
      inQuery (Inline p) = (_paramIn p) == ParamQuery

      -- create all the  StripeHasParam instances for this operation
      (params, stripeHasParamDecls') = unzip $ map (mkStripeHasParam opName mIdName) $ filter inQuery (_operationParameters op)
      stripeHasParamDecls =  stripeHasParamDecls' ++ instanceDecls {- ++ typeDecls'-}

      (returnImports, returnTy) =
            case InsOrd.lookup 200 (_responsesResponses (_operationResponses op)) of
              (Just (Inline resp)) -> responseType resp

      (requestDecl, requestTypes) = mkRequestDecl path method mIdName op requiredParams

      stripeReturnDecl = tyFamInst "StripeReturn" [var $ UnqualStr opName] returnTy

--      map referencedParamToDecl (_operationParameters $ fromJust $ _pathItemPost pi)
      addIdName =
        case mIdName of
          Nothing -> id
          (Just idName) -> (textToPascalName idName :)
  in (concat paramImports, (requestDecl ++ (opIdDecl:stripeReturnDecl:stripeHasParamDecls)),  addIdName (returnImports ++ params ++ reexports), [] {- requestTypes FIMXE -})


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

unzip3Concat :: [([a],[b],[c])] -> ([a],[b],[c])
unzip3Concat l =
  let (as, bs, cs) = unzip3 l
  in (concat as, concat bs, concat cs)


unzip4   :: [(a,b,c,d)] -> ([a],[b],[c],[d])
{-# INLINE unzip4 #-}
-- Inline so that fusion `foldr` has an opportunity to fire.
-- See Note [Inline @unzipN@ functions] in GHC/OldList.hs.
unzip4   =  foldr (\(a,b,c,d) ~(as,bs,cs,ds) -> (a:as,b:bs,c:cs,d:ds))
                  ([],[],[],[])

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
mkImport n =  import' (fromString $ "Web.Stripe.Component."  <> (rdrNameStrToString n)) `exposing` [ thingWith n []]

mkPaths :: OpenApi -- ^ openapi spec
        -> [(FilePath, Maybe Text)]    -- ^ path (e.g. \/v1\/account), what type is '{id}' in the path
        -> NonEmpty String    -- ^ module name -- just the last bit like 'Account'
        -> IO ()
mkPaths oa paths modBaseName =
  do let (pathImports, opDecls, reexportTypes, additionalExports) = unzip4Concat $ map (mkPath oa) paths
         requestBodyProperties =
           concatMap findPropertiesInPathItems (lookupPaths (_openApiPaths oa) paths)
         (propImports', propDecls') = unzip $ map (uncurry (schemaToTypeDecls AllDeclarations "FixMeMkPaths")) ([ (t, s) | (t, Inline s) <- requestBodyProperties ])
         (propImports, propDecls) = (nub $ concat propImports', concat propDecls')
         exports = Just (nub $ {- reexportTypes ++ -} (map var (additionalExports)))
         imports = [ import' "Data.Data" `exposing` [ var "Data" ]
                   , import' "Data.Text" `exposing` [ var "Text" ]
                   , import' "Web.Stripe.StripeRequest" `exposing`
                     [ thingAll "Method"
                     , thingWith "StripeHasParam" []
                     , thingAll "StripeRequest"
                     , var "StripeReturn"
                     , var "mkStripeRequest"
                     ]
                   , import' "Web.Stripe.Types" `exposing` (thingAll "Emptyable" : thingAll "ExpandParams" : thingAll "Metadata" : thingAll "StripeList" : thingAll "StartingAfter": thingAll "EndingBefore" : thingAll "Limit" : [] {- (nub reexportTypes) -} )
                   , import' "Web.Stripe.Util" `exposing` [var "(</>)"]
                   ] ++ (map mkImport (propImports ++ pathImports))
         modul  = module' (Just $ fromString $ "Web.Stripe." <> foldr1 (\a b -> a <> "." <> b) modBaseName) exports imports (opDecls ++ propDecls)
         extensions = [ FlexibleInstances
                      , MultiParamTypeClasses
                      , OverloadedStrings
                      , TypeFamilies
                      ]
     formatted <- showModule ("Web/Stripe/" <> foldr1 (\a b -> a <> "/" <> b) modBaseName <> ".hs") extensions modul True
--     T.putStr formatted
     let filepath = "_generated/src/Web/Stripe/" <> foldr1 (\a b -> a <> "/" <> b) modBaseName <> ".hs"
     createDirectoryIfMissing True (takeDirectory filepath)
     T.writeFile filepath formatted
     pure ()
  {-
  do let (Just pi) = InsOrd.lookup path (_openApiPaths oa)
         (Just op) = _pathItemGet pi
         (opDecls, reexports, additionalExports) = mkOperation path "GET" idName op
     let reexportTypes = map thingAll reexports

         imports = [ import' "Web.Stripe.StripeRequest" `exposing`
                     [ thingWith "Method" ["GET"]
                     , thingAll "StripeRequest"
                     , var "StripeReturn"
                     , var "mkStripeRequest" ]
                   , import' "Web.Stripe.Types" `exposing` reexportTypes
                   ]
         exports = Just (reexportTypes ++ (map var additionalExports))
-}

mkPath :: OpenApi -> (FilePath, Maybe Text) -> ([RdrNameStr], [HsDecl'], [IE'], [RdrNameStr])
mkPath oa (path, idName) =
  mkPath' oa GET  (path, idName) <>
  mkPath' oa POST (path, idName)
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
mkPath' :: OpenApi -> Method -> (FilePath, Maybe Text) -> ([RdrNameStr], [HsDecl'], [IE'], [RdrNameStr])
mkPath' oa method (path, idName) =
  let (Just pi) = InsOrd.lookup path (_openApiPaths oa)
      mop = case method of
                    GET  -> _pathItemGet pi
                    POST -> _pathItemPost pi
  in case mop of
        Nothing -> ([],[],[], [])
        (Just op) ->
          let (imports, opDecls, reexports, additionalExports) = mkOperation path method idName op
              reexportTypes = map thingAll (nub reexports)
--              exports = Just ({- reexportTypes ++ -} (map var additionalExports))
          in (imports, opDecls, reexportTypes, additionalExports)  -- FIXME: we used to define all the types in Web.Stripe.Types, but now some are defined locally


{-
      imports = [ import' "Web.Stripe.StripeRequest" `exposing`
                     [ thingWith "Method" ["GET"]
                     , thingAll "StripeRequest"
                     , var "StripeReturn"
                     , var "mkStripeRequest" ]
                   , import' "Web.Stripe.Types" `exposing` reexportTypes
                   ]
-}

mkFromJSON :: Text -> Schema -> HsDecl'
mkFromJSON name s =
  let properties = sortOn fst $ (InsOrd.toList (_schemaProperties s))
  in instance' (var "FromJSON" @@ (var $ textToPascalName name))
       [ funBinds "parseJSON" [ match [bvar "(Data.Aeson.Object o)"] $
                              case properties of
                                [] -> (var "pure") @@ (var "undefined") --  (var $ textToPascalName name)  -- FIXME
                                _  -> op' (var $ textToPascalName name) "<$>" $ addAp $ map (mkJsonField name) $ properties
                                                    ]
       , funBinds "parseJSON" [ match [wildP] (var "mzero") ]
       ]

op' :: HsExpr' -> RdrNameStr -> HsExpr' -> HsExpr'
op' x o y =
  OpApp  EpAnnNotUsed (mkLocated x) (mkLocated $ var o) (mkLocated y)

addAp :: [HsExpr'] -> HsExpr'
addAp [a] = a
addAp (a:rs) =  (op' a "<*>" (addAp rs))

mkJsonField :: Text -> (Text, Referenced Schema) -> HsExpr'
-- mkJsonField objName ("amount", (Inline s)) = par (op' (var "Amount") "<$>" (op (var "o") ".:"  (string "amount")))
-- mkJsonField objName ("amount_refunded", (Inline s)) = par (op' (var "Amount") "<$>" (op (var "o") ".:"  (string "amount_refunded")))
mkJsonField objName ("id", (Inline s)) = par (op' (var (textToPascalName $ objName <> "_id")) "<$>" (op (var "o") ".:"  (string "id")))
mkJsonField _ (fieldName, (Inline s)) =
  let oper = case _schemaNullable s of
               (Just True) -> ".:?"
               _           -> ".:"
      val = case () of
        () -- | (_schemaType s == Just OpenApiInteger) && (_schemaFormat s == Just "unix-time") ->
               -- par $ (var "fromSeconds") @@ (op (var "o") ".:" (string $ T.unpack fieldName))
           | otherwise -> (string $ T.unpack fieldName)
    in op' (var "o") oper val
mkJsonField _ (fieldName, (Ref r)) =
  op (var "o") ".:"  (string $ T.unpack fieldName)


-- create newtype, FromJSON and ExpandsTo for an id wrapped in a newtype
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
                    [ funBinds "parseJSON" [ match [ bvar "(String x)" ] $
                                             op' (var "pure") "$" ((var $ fromString $ T.unpack n) @@ var "x")
                                           , match [ wildP ] (var "mzero")
                                           ]
                    ]
                  , typeInstance' ("ExpandsTo "<> T.unpack (textToPascalName (baseName <> "_id")))  hsOuterImplicit [] Prefix (var $ fromString $ T.unpack $ textToPascalName baseName)
                  ]
             else []
      -- FIXME: this is definitely not the right way to call typeInstance'


-- create type declarations from 'Referenced Param'
mkParam :: Referenced Param -> [HsDecl']
mkParam (Ref r) = []
mkParam (Inline p) =
  [ newtype' (textToPascalName $ _paramName p) []
      (recordCon (textToPascalName $ _paramName p) []) derivingCommon
  ]

mkObject :: GenStyle -> (Text, Schema) -> ([RdrNameStr], [HsDecl'])
mkObject gs (objName', schema) =
  let objName = case objName' of
        "automatic_tax" ->  "automatic_tax_object"
        _               -> objName'
  in {- (mkFromJSON objName schema) : -}
      (schemaToTypeDecls gs objName objName schema)

mkComponents :: OpenApi -> IO ()
mkComponents oa =
  mapM_ mkComponent (InsOrd.toList (_componentsSchemas (_openApiComponents oa)))

breakCycle :: String -> RdrNameStr -> Bool
breakCycle "File" "FileLink" = True
breakCycle "Price" "Product" = True
breakCycle "Account" "ExternalAccount" = True
breakCycle _ "PaymentMethod" = True
breakCycle "Customer" "TaxId" = True
breakCycle "Customer" "Discount" = True
breakCycle "Customer" "PaymentSource" = True
breakCycle "Customer" "InvoiceSettingCustomerSetting" = True
breakCycle "Customer" "Subscription" = True
breakCycle "Charge" "PaymentSource" = True
breakCycle _        "ApiErrors" = True
breakCycle _        "PaymentSource" = True
breakCycle _        "FileLink" = True
breakCycle _        "ExternalAccount" = True
breakCycle _        "PaymentMethod" = True
breakCycle _        "TaxId" = True
breakCycle _        "Discount" = True
breakCycle _        "PaymentSource" = True
breakCycle _        "InvoiceSettingCustomerSetting" = True
breakCycle _        "Subscription" = True
breakCycle _        "Charge" = True
breakCycle _        "Transfer" = True
breakCycle _        "TransferReversal" = True
breakCycle _        "SetupAttempt" = True
breakCycle _        "PaymentIntent" = True
breakCycle _        "Account" = True
breakCycle _        "ApplicationFee" = True
breakCycle _        "Quote" = True
breakCycle _        "BalanceTransaction" = True
breakCycle _        "Invoice" = True
breakCycle _        "IssuingTransaction" = True


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
                                             , var "(.:)"
                                             , var "(.:?)"
                                             ]
           , import' "Data.Aeson.Types" `exposing` [ var "typeMismatch" ]
           , import' "Data.Data"  `exposing` [ var "Data", var "Typeable" ]
           , qualified' $ import' "Data.HashMap.Strict" `as'` "H"
           , import' "Data.Map"   `exposing` [ var "Map" ]
           , import' "Data.Ratio" `exposing` [ var "(%)" ]
           , import' "Data.Text"  `exposing` [ var "Text" ]
           , import' "Data.Time"  `exposing` [ var "UTCTime" ]
--           , import' "Numeric"  `exposing` [ var "fromRat" , var "showFFLoat" ]
           , import' "Text.Read"  `exposing` [ var "lexP", var "pfail" ]
           , qualified' $ import' "Text.Read" `as'` "R"
           , import' "Web.Stripe.OneOf" `exposing` [ thingAll "OneOf" ]
           , import' "Web.Stripe.Types"
           , import' "Web.Stripe.Util"  `exposing` [ var "fromSeconds" ]
           ]
         exports = Nothing
         (objectImports', objectDecls) = mkObject AllDeclarations component
         objectImports = map (\n -> sourceImport pname n $ import' (fromString $ "Web.Stripe.Component."  <> (rdrNameStrToString n)) {- `exposing` [ thingWith n [], thingWith (fromString $ (rdrNameStrToString n) <> "Id") []]-}) objectImports'
         decls = [ -- ExpandsTo
                 ] ++
                 objectDecls ++
                 concatMap (mkId AllDeclarations) (findIds' component) ++
--                 mkEnums (findEnums' component Map.empty) ++

                 []
         modul = module' (Just $ fromString ("Web.Stripe.Component." <> pname)) exports (staticImports ++ objectImports) decls

     formatted <- showModule ("Web/Stripe/Component/" <> pname) extensions modul True
     createDirectoryIfMissing True "_generated/src/Web/Stripe/Component/"
     T.writeFile ("_generated/src/Web/Stripe/Component/" <> pname <> ".hs") formatted
     when (name `elem` [] || True) $
       mkHsBoot component
     pure ()

mkHsBoot :: (Text, Schema) -> IO ()
mkHsBoot component@(name, schema)
  | name `elem` ["charge", "file_link", "external_account", "payment_method", "tax_id", "discount", "payment_source", "invoice_setting_customer_setting", "subscription", "transfer", "api_errors", "setup_attempt", "payment_intent", "transfer_reversal", "account", "application_fee", "quote", "balance_transaction", "invoice", "issuing_transaction"] =
  do let extensions = [ DataKinds
                      , DeriveDataTypeable
                      , FlexibleContexts
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
                                             , var "(.:)"
                                             , var "(.:?)"
                                             ]
           , import' "Data.Aeson.Types" `exposing` [ var "typeMismatch" ]
           , import' "Data.Data"  `exposing` [ var "Data", var "Typeable" ]
           , qualified' $ import' "Data.HashMap.Strict" `as'` "H"
           , import' "Data.Map"   `exposing` [ var "Map" ]
           , import' "Data.Ratio" `exposing` [ var "(%)" ]
           , import' "Data.Text"  `exposing` [ var "Text" ]
           , import' "Data.Time"  `exposing` [ var "UTCTime" ]
--           , import' "Numeric"  `exposing` [ var "fromRat" , var "showFFLoat" ]
           , import' "Text.Read"  `exposing` [ var "lexP", var "pfail" ]
           , qualified' $ import' "Text.Read" `as'` "R"
           , import' "Web.Stripe.OneOf" `exposing` [ thingAll "OneOf" ]
           , import' "Web.Stripe.Types"
           , import' "Web.Stripe.Util"  `exposing` [ var "fromSeconds" ]
           ]
         exports = Nothing
         (objectImports', objectDecls) = mkObject HsBoot component
         objectImports = mapMaybe (\n -> skipImport pname n $ import' (fromString $ "Web.Stripe.Component."  <> (rdrNameStrToString n))  `exposing` [ thingWith n []]) objectImports'
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

-- create Web.Stripe.Types
mkTypes :: OpenApi -> IO ()
mkTypes oa =
  do let extensions = [ DataKinds
                      , DeriveDataTypeable
                      , FlexibleContexts
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
                                             , thingWith "Value" [ "String", "Object", "Bool" ]
                                             , var "(.:)"
                                             , var "(.:?)"
                                             ]
           , import' "Data.Aeson.Types" `exposing` [ var "typeMismatch" ]
           , import' "Data.Data"  `exposing` [ var "Data", var "Typeable" ]
           , qualified' $ import' "Data.HashMap.Strict" `as'` "H"
           , import' "Data.Map"   `exposing` [ var "Map" ]
           , import' "Data.Ratio" `exposing` [ var "(%)" ]
           , import' "Data.Text"  `exposing` [ var "Text" ]
           , import' "Data.Time"  `exposing` [ var "UTCTime" ]
--           , import' "Numeric"  `exposing` [ var "fromRat" , var "showFFLoat" ]
           , import' "Text.Read"  `exposing` [ var "lexP", var "pfail" ]
           , qualified' $ import' "Text.Read" `as'` "R"
           , import' "Web.Stripe.OneOf" `exposing` [ thingAll "OneOf" ]
           , import' "Web.Stripe.Util"  `exposing` [ var "fromSeconds" ]
           ]
         exports = Nothing
-- charge         charge = (componentSchemaByName oa "charge")
         cs = _componentsSchemas (_openApiComponents oa)
         decls = [ -- ExpandsTo
                   typeFamily' OpenTypeFamily TopLevel "ExpandsTo" [bvar "id"] Prefix (KindSig NoExtField (hsStarTy False))
--                 , tyFamInst "ExpandsTo" [var "AccountId"] (var "Account")
                 -- fixme -- fake types
                 , data' "LineItems" []  [ prefixCon "LineItems" [] ] derivingCommon
--                 , data' "FixMe4b" []  [ prefixCon "FixMe4b" [] ] derivingCommon
--                 , data' "FixMe4bId" []  [ prefixCon "FixMe4bId" [] ] derivingCommon
--                 , typeInstance' "ExpandsTo FixMe4bId"  hsOuterImplicit [] Prefix (var "FixMe4bId")
                 , data' "UseStripeSdk" []  [ prefixCon "UseStripeSdk" [] ] derivingCommon
                 , instance' (var "FromJSON" @@ var "UseStripeSdk") [ funBinds "parseJSON" [ match []  (var "undefined")] ]
--                 , instance' (var "FromJSON" @@ var "StripeType") [ funBinds "parseJSON" [ match []  (var "undefined")] ]
                 , data' "Refunds" []  [ prefixCon "Refunds" [] ] derivingCommon
                 , data' "Expandable" [ bvar "id" ] [ prefixCon "Id" [ field $ var "id" ]
                                                    , prefixCon "Expanded"  [field $ var "ExpandsTo" @@ var "id"]
                                                    ] [ deriving' [ var "Typeable" ]]
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
                                                       op (op  (var "Id") "<$>" (var "parseJSON" @@ var "v"))
                                                          "<|>"
                                                          (op (var "Expanded") "<$>" (var "parseJSON" @@ var "v"))
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
                 , instance' (var "FromJSON" @@ (var "StripeList" @@ var "a")) [ funBinds "parseJSON" [ match []  (var "undefined")] ]
                 , newtype' "ExpandParams" [] (recordCon "ExpandParams" [ ( fromString "getExpandParams", field $ listTy (var "Text"))])  derivingCommon
                 , newtype' "EndingBefore" [ bvar "a" ] (recordCon "EndingBefore" [ ( fromString "getEndingBefore", field $ var "a") ])  derivingCommon
                 , newtype' "StartingAfter" [ bvar "a" ] (recordCon "StartingAfter" [ ( fromString "getStartingAfter", field $ var "a") ])  derivingCommon
                 , newtype' "Limit" [ ] (recordCon "Limit" [ ( fromString "getLimit", field $ var "Int") ])  derivingCommon
                 , newtype' "Metadata" [ ] (recordCon "Metadata" [ ( fromString "unMetadata", field $ listTy $ tuple [ var "Text", var "Text" ])])  derivingCommon
                 , data' "NowOrLater" [] [ prefixCon "Now" []
                                         , prefixCon "Later" [ strict $ field $ var "UTCTime" ]
                                         ] derivingCommon
                 , data' "Lines" [ bvar "a" ]
                    [ recordCon "Lines"
                       [ ("linesData"   , field $ listTy (var "a"))
                       , ("linesUrl"    , field $ var "Text")
                       , ("linesObject" , field $ var "Text")
                       , ("linesHasMore", field $ var "Bool")
                       ]
                    ]  derivingCommon
                 , data' "Emptyable" [ bvar "a" ]
                    [ prefixCon "Full"  [ strict $ field $ var "a" ]
                    , prefixCon "Empty" []
                    ] derivingCommon
{-
                 , type' "PaymentSourceId" [] (var "OneOf" @@ listPromotedTy [ var "AccountId"
                                                                             ] )
                 , type' "BalanceTransactionSourceId" [] (var "OneOf" @@ listPromotedTy
                                                                             [ var "ApplicationFeeId"
                                                                             ] )
-}
                 ] ++  map mkTimeNewtype timeNewtypes ++
                 [ {- data' "Currency" []
                    [ prefixCon "USD" [] -- FIXME, calculate entire list
                    ] [ deriving' [ var "Read"
                                  , var "Show"
                                  , var "Eq"
                                  , var "Ord"
                                  , var "Data"
                                  , var "Typeable"
                                  ]
                      ]

                 , -} newtype' "Amount" [] (recordCon "Amount" [ ("getAmount", field $ var "Int") ]) derivingCommon
                 , instance' (var "FromJSON" @@ var "Amount") [ funBinds "parseJSON" [ match []  (var "undefined")] ]
                   -- emptyTimeRange
                 , typeSig "emptyTimeRange" $ var "TimeRange" @@ var "a"
                 , funBind "emptyTimeRange" $ match [] (var "TimeRange" @@ var "Nothing" @@ var "Nothing" @@ var "Nothing" @@ var "Nothing" )
                 ] ++
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

showGhc a =
  runGhc (Just libdir) $
    do dflags <- getDynFlags
       pure $ showPpr dflags a

timeNewtypes = [ "AvailableOn", "Created", "Date" ]

findIds :: OpenApi -> [Text]
findIds oa =
  let cs = _componentsSchemas (_openApiComponents oa)
  in (concatMap findIds' $ InsOrd.toList cs)

findIds' :: (Text, Schema) -> [Text]
findIds' (obj, s) =
  case InsOrd.lookup "id" (_schemaProperties s) of
    Nothing -> []
    (Just _) -> [ obj ]

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
  case enum of
    -- if the enum is just these three fields, then we will just use the generic 'Status' enum
    [Aeson.String "active",Aeson.String "inactive",Aeson.String "pending"] ->
      enums
    _ ->
      Map.insertWith Set.union tyName (Set.fromList $ [ s | (Aeson.String s) <- enum]) enums
findEnums'  _ enums = enums
--findEnums' (tyName, s) _ = error $ show $ (tyName, ppSchema s)

mkEnums :: GenStyle -> Map Text (Set Text) -> [HsDecl']
mkEnums gs (Map.toList -> enums) = concatMap mkEnum $ {- filter (\(t,c) -> not $ "_payments" `T.isSuffixOf` t) -} enums
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
    mkEnum ("source", conNms) =
      [ data' (textToPascalName "customer_tax_location_source") [] [ mkCon "customer_tax_location_source" c | c <- Set.toList conNms ] (derivingCommon' gs)
      ]
    mkEnum (typeNm, conNms) =
      (data' (textToPascalName typeNm) [] [ mkCon typeNm c | c <- Set.toList conNms ] (derivingCommon' gs)) :
      if (gs == AllDeclarations)
      then [ instance' (var "FromJSON" @@ (var $ textToPascalName typeNm)) [ funBinds "parseJSON" [ match []  (var "undefined")] ]
           ]
      else []

main :: IO ()
main =
  do oa <- readSpec
--     let e = findEnums oa
--     print $ Map.keys e
     createDirectoryIfMissing True "_generated/src/Web/Stripe"
     copyFile "static/Web/Stripe/StripeRequest.hs" "_generated/src/Web/Stripe/StripeRequest.hs"
     copyFile "static/Web/Stripe/OneOf.hs" "_generated/src/Web/Stripe/OneOf.hs"
     copyFile "static/Web/Stripe/Util.hs" "_generated/src/Web/Stripe/Util.hs"

     mkTypes oa
     mkComponents oa
#if 0
     -- Web.Stripe.Account
     mkPaths oa [("/v1/account", Just "AccountId")] (NonEmpty.singleton "Account")

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
