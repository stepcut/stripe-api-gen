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
import Data.Aeson (decode')
import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy as LBS
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.HashMap.Strict.InsOrd as InsOrd
import Data.HashMap.Strict.InsOrd (InsOrdHashMap)
import Data.Maybe (fromJust, isJust, fromMaybe)
import Data.OpenApi
import qualified Data.List.NonEmpty as NonEmpty
import Data.String (IsString(fromString))
import Data.List (sortOn)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.SourceGen
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
import GHC.Hs.Type (LHsType, HsType(HsDocTy))
import GHC.Hs.Extension (GhcPs) -- Pass(Parsed), GhcPass(GhcPs))
import GHC.Types.SrcLoc (SrcSpan, Located, GenLocated(..), mkGeneralSrcSpan, mkRealSrcLoc)
import GHC.Types.Fixity (LexicalFixity(Prefix))
import GHC.Utils.Error (DiagOpts(..))
import GHC.Utils.Outputable (defaultSDocContext)
import System.FilePath (splitPath)
import Text.Casing (pascal, camel)
import Text.PrettyPrint.GenericPretty
import Text.PrettyPrint hiding ((<>))
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


-}

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

-- * Read Stripe spec

readSpec :: IO OpenApi
readSpec =
  do c <- LBS.readFile "./stripe-openapi3/openapi/spec3.json"
     case decode' c of
       Nothing -> error "could not decode' spec3.json"
       (Just o) -> pure o

mDocVar v Nothing = v
mDocVar v _ = v
 -- (Just txt) = docVar v (multiLineDocString HsDocStringPrevious $ NonEmpty.singleton (T.unpack txt))


referencedSchemaToType :: Text -> Referenced Schema -> (HsType', [HsDecl'])
referencedSchemaToType n (Inline s) = schemaToType n s
referencedSchemaToType n (Ref (Reference r)) = ((var $ textToPascalName r), [])

schemaToType :: Text -> Schema -> (HsType', [HsDecl'])
schemaToType n s =
  let (ty, decls) = schemaToType' n s
  in case _schemaNullable s of
    (Just True) -> (var "Maybe" @@ ty, decls)
    _           -> (ty, decls)

schemaToEnumDecl :: Text -> Schema -> (HsType', [HsDecl'])
schemaToEnumDecl nm s
  | _schemaType s == Just OpenApiString =
      case _schemaEnum s of
        (Just vs) ->
          let occNam = pascal $ T.unpack $ nm
              cons = [ prefixCon (fromString $ pascal $ T.unpack c) [] | (Aeson.String c) <- vs ]
          in (var (fromString occNam), [data' (fromString occNam) [] cons commonDeriving])
        Nothing ->
          let typName = textToPascalName nm
              cons     = [ recordCon (fromString $ textToPascalName nm) [ ((fromString $ "un" <> textToPascalName nm)
                                                                          , (strict $ field $ var (fromString "Text"))
                                                                          )
                                                                        ]
                         ]
          in (var (fromString typName) , [data' (fromString typName) [] cons commonDeriving])

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

schemaToType' :: Text -> Schema -> (HsType', [HsDecl'])
schemaToType' n s
  | (_schemaType s == Just OpenApiInteger) && (_schemaFormat s == Just "unix-time") =
      (var "UTCTime", [])
  | (_schemaType s == Just OpenApiInteger) =
      case _schemaFormat s of
        (Just "int32") -> (var "Int32", [])
        (Just "int64") -> (var "Int64", [])
        _              -> (var "Integer", [])
  | (_schemaType s == Just OpenApiBoolean) =
      (var "Bool", [])
  | (_schemaType s == Just OpenApiNumber) =
      case _schemaFormat s of
        (Just "float")  -> (var "Float", [])
        (Just "double") -> (var "Double", [])
        _               -> (var "Double", [])
  | (_schemaType s == Just OpenApiString) =
    case n of
      "currency" -> (var "Currency", [])
      "object"   -> (var "Text", [])
      _ -> case _schemaEnum s of
            Nothing -> (var "Text", [])
            _       -> schemaToEnumDecl n s
  | (_schemaType s == Just OpenApiArray) =
      case _schemaItems s of
        Just (OpenApiItemsObject (Ref (Reference r))) ->
          (var "StripeList" @@ (var $ textToPascalName r), [])
        Just (OpenApiItemsObject (Inline s)) ->
          let (ty, decls) = schemaToType' "FixMe4" s
          in (var "StripeList" @@ ty, decls)
        Nothing -> (var "FixMeOpenApiItemsObject", [])
  | (_schemaType s == Just OpenApiObject) =
      case (_schemaAdditionalProperties s) of
        (Just (AdditionalPropertiesSchema rSchema)) ->
          let (ty, decls) = referencedSchemaToType n rSchema
          in (var (fromString "Map") @@ var (fromString "Text") @@ ty, decls)
        _ ->
          (var (fromString $ textToPascalName n), schemaToTypeDecls n s)
  | isJust (_schemaAnyOf s) =
      case _schemaAnyOf s of
        (Just [(Inline schema1), (Ref (Reference r))])
          | (_schemaType schema1) == Just OpenApiString ->
              (var "Expandable" @@ (var $ fromString $ textToPascalName (r <> "_id")), [])
        _ -> -- TODO: if anyOf only has one field should we still use it?
          let (Just schemas) = _schemaAnyOf s
              (types, decls) = unzip $ map (referencedSchemaToType "FixMe7") schemas
          in (var "OneOf" @@ listPromotedTy types, concat decls)
schemaToType' n s = error $ show $ (n, ppSchema s)
-- schemaToType' _ _ = (var "FixMe", [])

textToOccName = fromString . T.unpack

schemaToField :: Text -> (Text, Referenced Schema) -> ((OccNameStr, Field), [HsDecl'])
schemaToField objectName (n, Inline s)
  | n == "id" && _schemaType s == Just OpenApiString =
      ((fromString $ textToCamelName (objectName <> "_" <> n), strict $ field $ var (fromString $ textToPascalName (objectName <> "_id"))), [])

-- schemaToField _ (n , Ref _)   = ((textToOccName n, strict $ field $ var "FixMe3"), [])
schemaToField objectName (n , Ref (Reference r))   = ((fromString $ textToCamelName(objectName <> "_" <> n), strict $ field $ var $ textToPascalName r ), [])
schemaToField objectName (n, Inline s) =
  let (ty, decls) = schemaToType n s
  in ((fromString $ camel $ T.unpack (objectName <> "_" <> n), strict $ field ty) , decls)

commonDeriving = [deriving' [ var "Eq", var "Data", var "Ord", var "Read", var "Show"]]


-- only for record types
schemaToTypeDecls :: Text -> Schema -> [HsDecl']
schemaToTypeDecls tyName s
  | _schemaType s == Just OpenApiString =
      (snd $ schemaToEnumDecl tyName s)
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
        _ ->
          let (Just schemas) = _schemaAnyOf s
              (types, decls) = unzip $ map (referencedSchemaToType "FixMe 6") schemas
--          decls = [] -- map schemaToTypeDecls 
              occName   = fromString (textToPascalName tyName)
              conName   = fromString (textToPascalName tyName)
              unConName = fromString ("un" <> textToPascalName tyName)
              cons = [ recordCon conName [ (unConName, strict $ field $ (var "OneOf" @@ listPromotedTy types)) ] ]
          in (data' occName [] cons commonDeriving) : concat decls
  | otherwise =
      let occName = fromString (textToPascalName tyName)
--          (fields, decls) =  unzip $ map (schemaToField (fromMaybe "FixMe2b" (_schemaTitle s))) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
          (fields, decls) =  unzip $ map (schemaToField (tyName)) $ sortOn fst $ (InsOrd.toList (_schemaProperties s))
          con = recordCon occName fields
      in (data' occName [] [con] commonDeriving) : concat decls
{-
  | otherwise = error $ "schemaToTypeDecls: " ++ show (tyName, ppSchema s)
-}

textToPascalName :: (IsString a) => Text -> a
textToPascalName = fromString . pascal . T.unpack

textToCamelName :: (IsString a) => Text -> a
textToCamelName = fromString . camel . T.unpack


referencedParamToDecl :: Referenced Param -> HsDecl'
referencedParamToDecl (Inline p) =
  paramToDecl p
{-
  let occName = textToPascalName $ _paramName p
  in data' occName [] (paramToConDecls (_paramName p) (_paramSchema p)) commonDeriving
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
  in data' occName [] (paramToConDecls (_paramName p) schema) commonDeriving

{-
ppReferenced :: Referenced Schema -> Doc
ppReferenced (Inline s) = text "Inline (" <+> ppSchema s <+> rparen
ppReferenced (Ref r) = text "Ref (" <+> text (show r) <+> text ")"
-}

ppSchemaProperty (n, s) =
  lparen <+> text (show  n) <+> comma <+> (ppReferenced ppSchema) s

ppSchemaProperties ps =
  case InsOrd.toList ps of
    [] -> text "[]"
    sp -> text "[" <+> (vcat (punctuate ", " (map ppSchemaProperty sp))) <+> text "]" 

ppSchema :: Schema -> Doc
ppSchema s =
  text "Schema" $+$ nest 2 (
   text "{ _schemaTitle = " <> text (show $ _schemaTitle s) $$
   text ", _schemaDescription = " <> text (show $ _schemaDescription s) $$
   text ", _schemaRequired = " <> text (show $ _schemaRequired s) $$
   text ", _schemaNullable = " <> text (show $ _schemaNullable s) $$
   text ", _schemaAllOf = " <> text (show $ _schemaAllOf s) $$
   text ", _schemaOneOf = " <> text (show $ _schemaOneOf s) $$
   text ", _schemaNot = " <> text (show $ _schemaNot s) $$
   text ", _schemaAnyOf = " <>
      (case _schemaAnyOf s of
        Nothing -> text "Nothing"
        (Just ss) -> text "Just [" <+> vcat (punctuate ", " (map (ppReferenced ppSchema) ss)) <+> text "]") $$
   text ", _schemaProperties = " <> ppSchemaProperties (_schemaProperties s) $$
   text ", _schemaAdditionalProperties = " <> text (show $ _schemaAdditionalProperties s) $$
   text ", _schemaReadOnly = " <> text (show $ _schemaReadOnly s) $$
   text ", _schemaWriteOnly = " <> text (show $ _schemaWriteOnly s) $$
   text ", _schemaXml = " <> text (show $ _schemaXml s) $$
   text ", _schemaExternalDocs = " <> text (show $ _schemaExternalDocs s) $$
   text ", _schemaExample = " <> text (show $ _schemaExample s) $$
   text ", _schemaDeprecated = " <> text (show $ _schemaDeprecated s) $$
   text ", _schemaMaxProperties = " <> text (show $ _schemaMaxProperties s) $$
   text ", _schemaMinProperties = " <> text (show $ _schemaMinProperties s) $$
   text ", _schemaDefault = " <> text (show $ _schemaDefault s) $$
   text ", _schemaType = " <> text (show $ _schemaType s) $$
   text ", _schemaFormat = " <> text (show $ _schemaFormat s) $$
   text ", _schemaItems = " <> text (show $ _schemaItems s) $$
   text ", _schemaMaximum = " <> text (show $ _schemaMaximum s) $$
   text ", _schemaExclusiveMaximum = " <> text (show $ _schemaExclusiveMaximum s) $$
   text ", _schemaMinimum = " <> text (show $ _schemaMinimum s) $$
   text ", _schemaExclusiveMinimum = " <> text (show $ _schemaExclusiveMinimum s) $$
   text ", _schemaMaxLength = " <> text (show $ _schemaMaxLength s) $$
   text ", _schemaMinLength = " <> text (show $ _schemaMinLength s) $$
   text ", _schemaPattern = " <> text (show $ _schemaPattern s) $$
   text ", _schemaMaxItems = " <> text (show $ _schemaMaxItems s) $$
   text ", _schemaMinItems = " <> text (show $ _schemaMinItems s) $$
   text ", _schemaUniqueItems = " <> text (show $ _schemaUniqueItems s) $$
   text ", _schemaEnum = " <> text (show $ _schemaEnum s) $$
   text ", _schemaMultipleOf = " <> text (show $ _schemaMultipleOf s) $$
   text "}"
   )

ppReferenced :: (a -> Doc) -> Referenced a -> Doc
ppReferenced pa (Inline a) = text "Inline (" <> (pa a) <> text ")"
ppReferenced pa (Ref (Reference t)) = text "Ref (" <> text (T.unpack t) <> text ")"

ppMaybe :: (a -> Doc) -> Maybe a -> Doc
ppMaybe pa Nothing = empty
ppMaybe pa (Just a) = lparen <> text "Just " <> pa a <> rparen

ppParam :: Param -> Doc
ppParam p =
  text "Param" $+$ nest 2 (
   text "{ _paramName = " <> text (show $ _paramName p) $$
   text ", _paramDescription = " <> text (show $ _paramDescription p) $$
   text ", _paramRequired = " <> text (show $ _paramRequired p) $$
   text ", _paramDeprecated = " <> text (show $ _paramDeprecated p) $$
   text ", _paramIn = " <> text (show $ _paramIn p) $$
   text ", _paramAllowEmptyValue = " <> text (show $ _paramAllowEmptyValue p) $$
   text ", _paramAllowReserved = " <> text (show $ _paramAllowReserved p) $$
   text ", _paramSchema = " <> ppMaybe (ppReferenced ppSchema) (_paramSchema p) $$
   text ", _paramStyle = " <> text (show $ _paramStyle p) $$
   text ", _paramExplode = " <> text (show $ _paramExplode p) $$
   text ", _paramExample = " <> text (show $ _paramExample p) $$
   text ", _paramExamples = " <> text (show $ _paramExamples p) $$
   text "}")

ppList :: [Doc] -> Doc
ppList docs = "[" <+> vcat (punctuate "," docs) <+> text "]"


ppRequestBody :: RequestBody -> Doc
ppRequestBody b =
  text "RequestBody" $+$ nest 2 (
   text "{ _requestBodyDescription = " <> text (show $ _requestBodyDescription b) $$
   text ", _requestBodyContent = " <> text (show $ _requestBodyContent b) $$
   text ", _requestBodyRequired = " <> text (show $ _requestBodyRequired b) $$
   text "}")


ppMediaTypeObject :: MediaTypeObject -> Doc
ppMediaTypeObject m =
  text "MediaTypeObject" $+$ nest 2 (
   text "{ _mediaTypeObjectSchema = " <> ppMaybe (ppReferenced ppSchema) (_mediaTypeObjectSchema m) $$
   text ", _mediaTypeObjectExample = " <> text (show $ _mediaTypeObjectExample m) $$
   text ", _mediaTypeObjectExamples = " <> text (show $ _mediaTypeObjectExamples m) $$
   text ", _mediaTypeObjectEncoding = " <> text (show $ _mediaTypeObjectEncoding m) $$
   text "}")

-- ppContent :: InsOrdHashMap MediaType MediaTypeObject -> Doc
ppContent c = ppList $ map (\(mt, mto) -> lparen <> text (show mt) <> text ", " <> ppMediaTypeObject mto <> rparen) (InsOrd.toList c)

ppResponse :: Response -> Doc
ppResponse r =
  text "Response" $+$ nest 2 (
   text "{ _responseDescription = " <> text (show $ _responseDescription r) $$
   text ", _responseContent = " <> ppContent (_responseContent r) $$
   text ", _responseHeaders = " <> text (show $ _responseHeaders r) $$
   text ", _responseLinks = " <> text (show $ _responseLinks r) $$
   text "}")

ppResponses :: Responses -> Doc
ppResponses r =
  text "Responses" $+$ nest 2 (
   text "{ _responsesDefault   = " <> ppMaybe (ppReferenced ppResponse) (_responsesDefault r) $$
   text ", _responsesResponses = " <> ppList (map (\(hsc, rr) ->
                                                  lparen <> text (show hsc) <> text ", " <> (ppReferenced ppResponse rr) <> rparen
                                               ) (InsOrd.toList $ _responsesResponses r)) $$
   text "}")

ppOperation :: Operation -> Doc
ppOperation s =
  text "Operation" $+$ nest 2 (
   text "{ _operationTags = " <> text (show $ _operationTags s) $$
   text ", _operationSummary = " <> text (show $ _operationSummary s) $$
   text ", _operationDescription = " <> text (show $ _operationDescription s) $$
   text ", _operationExternalDocs = " <> text (show $ _operationExternalDocs s) $$
   text ", _operationOperationId = " <> text (show $ _operationOperationId s) $$
   text ", _operationParameters = " <> ppList (map (ppReferenced ppParam) (_operationParameters s)) $$
   text ", _operationRequestBody = " <> ppMaybe (ppReferenced ppRequestBody) (_operationRequestBody s) $$
   text ", _operationResponses = " <> ppResponses (_operationResponses s) $$
   text ", _operationCallbacks = " <> text (show $ _operationCallbacks s) $$
   text ", _operationDeprecated = " <> text (show $ _operationDeprecated s) $$
   text ", _operationSecurity = " <> text (show $ _operationSecurity s) $$
   text ", _operationServers = " <> text (show $ _operationServers s) $$
   text "}")




subscriptionSchema :: OpenApi -> Schema
subscriptionSchema o =
  case InsOrd.lookup "subscription" (_componentsSchemas (_openApiComponents o)) of
    Nothing -> error "could not find subsription schema"
    (Just s) -> s

data Method = GET | POST | DELETE
  deriving (Eq, Ord, Read, Show)


mkStripeHasParam :: OccNameStr -> Referenced Param -> HsDecl'
mkStripeHasParam opName (Inline param) =
  instance' (var "StripeHasParam" @@ (var $ UnqualStr opName) @@ (var (textToPascalName $ _paramName param))) []

mkStripeHasParamFromProperty :: OccNameStr -> (Text, (Referenced Schema)) -> [(HsDecl', InsOrdHashMap Text [HsDecl'])]
mkStripeHasParamFromProperty opName (pName, (Inline schema)) =
  let inst = instance' (var "StripeHasParam" @@ (var $ UnqualStr opName) @@ (var (textToPascalName $ pName))) []
      tys = InsOrd.fromList [(pName, schemaToTypeDecls pName schema)]
  in [(inst, tys)]


mkStripeRequestBodyStripeHasParam :: OccNameStr -> Maybe (Referenced RequestBody) -> [(HsDecl', InsOrdHashMap Text [HsDecl'])]
mkStripeRequestBodyStripeHasParam opName Nothing = []
mkStripeRequestBodyStripeHasParam opName (Just (Inline rb)) =
  case InsOrd.lookup "application/x-www-form-urlencoded" (_requestBodyContent rb) of
    Nothing -> []
    (Just mto) ->
      case _mediaTypeObjectSchema mto of
        (Just (Inline schema)) ->
          concatMap (mkStripeHasParamFromProperty opName) (InsOrd.toList (_schemaProperties schema ))


responseType :: Response -> HsType'
responseType resp =
  case InsOrd.lookup "application/json" (_responseContent resp) of
    Nothing -> error $ "responseType: could not find application/json for response " <> show (ppResponse resp)
    (Just mto) ->
      case _mediaTypeObjectSchema mto of
        (Just (Inline schema)) ->
          case InsOrd.lookup "data" (_schemaProperties schema) of
            (Just (Inline dataSchema)) ->
              fst $ schemaToType "FixMeResponseType" dataSchema
            Nothing ->
              case _schemaAnyOf schema of
                (Just anyOf) ->
                  var "OneOf" @@ (listPromotedTy $ map (\(Ref (Reference s)) -> var $ textToPascalName s) anyOf)
                Nothing ->
                  do error $ "Could not find schemaProperty named 'data'\n " <> show (ppSchema schema)
        (Just (Ref (Reference s))) ->
          var (textToPascalName s)

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

mkPathTemplate :: PathTemplate -> (Maybe (Pat', HsType'), HsExpr')
mkPathTemplate (PathStatic static) = (Nothing, string (T.unpack static))
mkPathTemplate (PathSubst subst)   =
  ( Just ( bvar (textToCamelName (subst <> "Id"))
         , var (textToPascalName (subst <> "Id"))
         )
  , var (fromString ("un" <> (pascal $ T.unpack subst) <> "Id")) @@ var (textToCamelName (subst <> "Id"))
  )

mkUrl :: [PathTemplate] -> ([(Pat', HsType')], HsExpr')
mkUrl [] = error "mkUrl: Can't create something from nothing."
mkUrl [pt] =
  case mkPathTemplate pt of
    (Nothing, exp) -> ([], exp)
    (Just (pat, typ), exp) ->
      ([(pat, typ)], exp)
mkUrl (pt:pts) =
  let (mPatTy, expl) = mkPathTemplate pt
      (patTys, expr) = mkUrl pts
      patTys' = case mPatTy of
        Nothing -> patTys
        (Just patTy) -> (patTy:patTys)
  in (patTys', op expl "</>" expr)

mkRequestDecl :: Text -> Text -> Operation -> [HsDecl']
mkRequestDecl path method oper =
  let opName :: OccNameStr
      opName   = textToCamelName $ fromJust $ _operationOperationId oper

      opName' :: RdrNameStr
      opName'  = textToPascalName $ fromJust $ _operationOperationId oper

      request = valBind "request" (var "mkStripeRequest" @@ var (fromString $ T.unpack method) @@ var "url" @@ var "params")
      pathTemplate = extractTemplate path
      (patTys, urlE) = mkUrl pathTemplate
--      (pats, typs) :: ([Pat'], [HsType'])
      (pats, typs) = unzip patTys
      url = valBind "url" urlE

      ty :: HsType'
      ty = foldr (\a b -> a --> b) (var "StripeRequest" @@ var opName') typs

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
  in  [ typeSig opName ty
      , funBind opName (matchGRHSs pats (rhs (var "request") `where'` [request, url, params]))
      ]

mkOperation :: Text -> Text -> Operation -> [HsDecl']
mkOperation path method op =
  let opName :: OccNameStr
      opName   = textToPascalName $ fromJust $ _operationOperationId op
      opIdDecl = data' opName [] [] []
      (instanceDecls, typeDecls) = unzip $ mkStripeRequestBodyStripeHasParam opName (_operationRequestBody op)
      typeDecls' :: [HsDecl']
      typeDecls' = concatMap snd $ concatMap InsOrd.toList typeDecls
      stripeHasParamDecls = map (mkStripeHasParam opName) (_operationParameters op) ++ instanceDecls ++ typeDecls'

      returnTy =
            case InsOrd.lookup 200 (_responsesResponses (_operationResponses op)) of
              (Just (Inline resp)) -> responseType resp

      requestDecl = mkRequestDecl path method op

      stripeReturnDecl = tyFamInst "StripeReturn" [var $ UnqualStr opName] returnTy

--      map referencedParamToDecl (_operationParameters $ fromJust $ _pathItemPost pi)
  in (requestDecl ++ (opIdDecl:stripeReturnDecl:stripeHasParamDecls))


main :: IO ()
main =
  do s <- readSpec
     let componentName = "application_fee"
         (Just comp) = InsOrd.lookup componentName $ _componentsSchemas (_openApiComponents s)

     let cs :: [(Text, Schema)]
         cs = InsOrd.toList (_componentsSchemas (_openApiComponents s))
         decls = concatMap (\(n,s) -> schemaToTypeDecls n s) [(componentName, comp)]

     print $ ppSchema comp
     runGhc (Just libdir) $ putPpr $
       module' (Just $ textToPascalName componentName) Nothing [] decls
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
