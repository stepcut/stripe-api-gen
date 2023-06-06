{-# language CPP #-}
{-# language DataKinds #-}
{-# language TypeFamilies #-}
{-# language OverloadedStrings #-}
module Extra where

import Data.String (fromString)
import GHC.Hs
import GHC.Hs.Decls
import GHC.Hs.Extension (GhcPs)
import GHC.SourceGen.Type (HsTyVarBndr')
import GHC.Types.Basic(TopLevelFlag)
import GHC.Types.Fixity (LexicalFixity)
import GHC.Types.SrcLoc (SrcSpan, GenLocated(L), mkGeneralSrcSpan)
import GHC.Types.Name.Reader (RdrName(..))
import GHC.Types.Name.Occurrence (mkTcOccFS)
import Language.Haskell.Syntax.Extension (NoExtField(NoExtField))
#if MIN_VERSION_ghc(9,2,0)
import GHC.Parser.Annotation (AnnSortKey(..), EpAnn(..))
#elif MIN_VERSION_ghc(8,10,0)
import GHC.Hs.Extension (NoExtField(NoExtField))
#elif MIN_VERSION_ghc(8,6,0)
import GHC.Hs.Extension (NoExt(NoExt))
#else
import PlaceHolder (PlaceHolder(..))
#endif

#if MIN_VERSION_ghc(9,2,0)
import GHC.Parser.Annotation (LocatedN)
#elif MIN_VERSION_ghc(9,0,0)
import GHC.Types.SrcLoc (SrcSpan, Located)
#else
import SrcLoc (Located)
#endif

#if MIN_VERSION_ghc(9,0,0)
import GHC.Data.FastString (FastString, fsLit)
import GHC.Unit.Module (mkModuleNameFS, ModuleName, moduleNameString)
import GHC.Types.Name.Occurrence
import GHC.Types.Name.Reader
#else
import FastString (FastString, fsLit)
import Module (mkModuleNameFS, ModuleName, moduleNameString)
import OccName
import RdrName
#endif

-- import GHC.SourceGen.Binds.Internal
--import GHC.SourceGen.Lit.Internal (noSourceText)
import GHC.SourceGen.Name
--import GHC.SourceGen.Name.Internal
--import GHC.SourceGen.Syntax.Internal
--import GHC.SourceGen.Type.Internal

type FamilyInfo' = FamilyInfo GhcPs
type LHsQTyVars' = LHsQTyVars GhcPs
type LFamilyResultSig' = LFamilyResultSig GhcPs
type FamilyResultSig' = FamilyResultSig GhcPs
type HsKind' = HsKind GhcPs

{-
valueOccName, typeOccName :: OccNameStr -> OccName
valueOccName (OccNameStr Constructor s) = mkDataOccFS s
valueOccName (OccNameStr Value s) = mkVarOccFS s
typeOccName (OccNameStr Constructor s) = mkTcOccFS s
typeOccName (OccNameStr Value s) = mkTyVarOccFS s

valueRdrName, typeRdrName :: RdrNameStr -> LocatedN RdrName
valueRdrName (UnqualStr r) = mkLocated $ Unqual $ valueOccName r
valueRdrName (QualStr (ModuleNameStr m) r) = mkLocated $ Qual m $ valueOccName r
typeRdrName (UnqualStr r) = mkLocated $ Unqual $ typeOccName r
typeRdrName (QualStr (ModuleNameStr m) r) = mkLocated $ Qual m $ typeOccName r
-}
builtSpan :: SrcSpan
builtSpan = mkGeneralSrcSpan "<ghc-source-gen>"

-- builtLoc :: e -> Located e
-- builtLoc = L builtSpan
{-
#if MIN_VERSION_ghc(9,2,0)
type SrcSpanAnn ann = GHC.SrcSpanAnn' (EpAnn ann)
#else
type SrcSpanAnn ann = SrcSpan
#endif
-}
mkLocated :: a -> GenLocated (SrcSpanAnn'  (EpAnn ann)) a
mkLocated = L (toAnn builtSpan)
  where
#if MIN_VERSION_ghc(9,2,0)
    toAnn = SrcSpanAnn EpAnnNotUsed
#else
    toAnn = id
#endif


withPlaceHolder = id

noExt :: (NoExtField -> a) -> a
noExt = ($ NoExtField)


mkQTyVars :: [HsTyVarBndr'] -> LHsQTyVars'
mkQTyVars vars =  withPlaceHolder
                $ noExt (withPlaceHolder HsQTvs)
                $ map mkLocated vars

-- hsStarTy :: Bool -> LHsKind'
hsStarTy b = mkLocated $ HsStarTy NoExtField b

family' :: FamilyInfo' -> TopLevelFlag -> String -> [HsTyVarBndr'] -> LexicalFixity -> FamilyResultSig' -> HsDecl GhcPs
family' fi tlf name vars fixity res =
  TyClD NoExtField $ FamDecl
          { tcdFExt = NoExtField
          , tcdFam  = FamilyDecl { fdExt       = EpAnnNotUsed
                                 , fdInfo      = fi
                                 , fdTopLevel  = tlf
                                 , fdLName     = mkLocated $ Unqual $ mkTcOccFS (fromString name)
                                 , fdTyVars    = mkQTyVars vars
                                 , fdFixity    = fixity
                                 , fdResultSig = mkLocated res
                                 , fdInjectivityAnn = Nothing
                                 }
          }
