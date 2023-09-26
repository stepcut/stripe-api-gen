{-# language OverloadedStrings #-}
module Pretty where

import qualified Data.HashMap.Strict.InsOrd as InsOrd
import Data.HashMap.Strict.InsOrd (InsOrdHashMap)
import Data.OpenApi
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Text.PrettyPrint.GenericPretty
import Text.PrettyPrint hiding ((<>))

{-
ppReferenced :: Referenced Schema -> Doc
ppReferenced (Inline s) = text "Inline (" <+> ppSchema s <+> rparen
ppReferenced (Ref r) = text "Ref (" <+> text (show r) x<+> text ")"
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
   text ", _schemaMultipleOf = " <> text (show $ _schemaMultipleOf s) $$
   text ", _schemaExtensions = " <> text (show $ _schemaExtensions s) $$
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
