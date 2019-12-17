-- Copyright (c) 2019 The DAML Authors. All rights reserved.
-- SPDX-License-Identifier: Apache-2.0

module DA.Daml.LF.Ast.Tests
    ( main
    ) where

import Control.Monad (unless)
import Data.Foldable
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.NameMap as NM
import Text.Read
import Test.Tasty
import Test.Tasty.HUnit

import DA.Daml.LF.Ast.Base
import DA.Daml.LF.Ast.Numeric
import DA.Daml.LF.Ast.Type
import DA.Daml.LF.Ast.Util
import DA.Daml.LF.Ast.Version
import DA.Daml.LF.Ast.World (initWorld)
import DA.Daml.LF.TypeChecker (checkModule)
import DA.Pretty (renderPretty)

main :: IO ()
main = defaultMain $ testGroup "DA.Daml.LF.Ast"
    [ numericTests
    , substitutionTests
    , typeSynTests
    ]

numericExamples :: [(String, Numeric)]
numericExamples =
    [ ("0.", numeric 0 0)
    , ("42.", numeric 0 42)
    , ("-100.", numeric 0 (-100))
    , ("100.00", numeric 2 10000)
    , ("123.45", numeric 2 12345)
    , ("1.0000", numeric 4 10000)
    , ("1.2345", numeric 4 12345)
    , ("0." ++ replicate 32 '0' ++ "54321", numeric 37 54321)
    , ("-9." ++ replicate 37 '9', numeric 37 (1 - 10^(38::Int)))
    ]

numericTests :: TestTree
numericTests = testGroup "Numeric"
    [ testCase "show" $ do
        for_ numericExamples $ \(str,num) -> do
            assertEqual "show produced wrong string" str (show num)
    , testCase "read" $ do
        for_ numericExamples $ \(str,num) -> do
            assertEqual "read produced wrong numeric or failed" (Just num) (readMaybe str)
    ]


substitutionTests :: TestTree
substitutionTests = testGroup "substitution"
    [ testCase "TForall" $ do
        let subst = Map.fromList [(beta11, vBeta1)]
            ty1 = TForall (beta11, KStar) $ TForall (beta1, KStar) $
                TBuiltin BTArrow `TApp` vBeta11 `TApp` vBeta1
            ty2 = substitute subst ty1
        assertBool "wrong substitution" (alphaEquiv ty1 ty2)
    ]
  where
    beta1 = TypeVarName "beta1"
    beta11 = TypeVarName "beta11"
    vBeta1 = TVar beta1
    vBeta11 = TVar beta11

typeSynTests :: TestTree
typeSynTests =
  testGroup "typecheck-after-synonym-expansion"
  [ testGroup "happy" (map mkHappyTestcase happyExamples)
  , testGroup "sad" (map mkSadTestcase sadExamples)
  ] where

  happyExamples :: [(Type,Type)]
  happyExamples =
    [ (TInt64, TInt64)
    , (TParty, TParty)
    , (TSyn (q myInt), TInt64)
    , (TSyn (q myMyInt), TInt64)
    , (TSyn (q myMyInt), TSyn (q myMyInt))
    , (TSyn (q myPairIP), mkPair TInt64 TParty)
    , (TSyn (q myPairIP), mkPair (TSyn (q myMyInt)) TParty)
    ]

  sadExamples :: [(Type,Type,String)]
  sadExamples =
    [ (TInt64, TParty, "type mismatch")
    , (TParty, TInt64, "type mismatch")
    , (TSyn (q missing), TInt64, "unknown type synonym: M:Missing")
    , (TSyn (q myInt), TParty, "type mismatch")
    , (TSyn (q myPairIP), mkPair TParty TInt64, "type mismatch")
    ]

  synDefs :: [DefTypeSyn]
  synDefs =
    [ makeSynDef myInt TInt64
    , makeSynDef myMyInt (TSyn (q myInt))
    , makeSynDef myPairIP (mkPair TInt64 TParty)
    ]

  moduleName :: ModuleName
  moduleName = ModuleName ["M"]

  q :: a -> Qualified a
  q = Qualified PRSelf moduleName

  missing = TypeSynName ["Missing"]
  myInt = TypeSynName ["MyInt"]
  myMyInt = TypeSynName ["MyMyInt"]
  myPairIP = TypeSynName ["MyPairIP"]

  mkPair ty1 ty2 = TStruct [(FieldName "fst",ty1),(FieldName "snd",ty2)]

  makeSynDef :: TypeSynName -> Type -> DefTypeSyn
  makeSynDef synName synType =
    DefTypeSyn { synLocation = Nothing , synName , synParams = [] , synType}

  mkHappyTestcase :: (Type,Type) -> TestTree
  mkHappyTestcase (ty1,ty2) = do
    let name = renderPretty ty1 <> " == " <> renderPretty ty2
    testCase name $ expectTypeCheckPass ty1 ty2

  expectTypeCheckPass :: Type -> Type -> IO ()
  expectTypeCheckPass t1 t2 = do
    let mod = makeModuleToTestTypeSyns t1 t2
    case typeCheck mod of
      Left s -> assertFailure $ "unexpected type error: " <> s
      Right () -> return ()

  mkSadTestcase :: (Type,Type,String) -> TestTree
  mkSadTestcase (ty1,ty2,frag) = do
    let name = renderPretty ty1 <> " =/= " <> renderPretty ty2
    testCase name $ expectTypeCheckFail ty1 ty2 (Fragment frag)

  expectTypeCheckFail :: Type -> Type -> Fragment -> IO ()
  expectTypeCheckFail t1 t2 errorFrag = do
    let mod = makeModuleToTestTypeSyns t1 t2
    case typeCheck mod of
      Left s -> assertStringContains s errorFrag
      Right () -> assertFailure "expected type error, but got none"

  makeModuleToTestTypeSyns :: Type -> Type -> Module
  makeModuleToTestTypeSyns ty1 ty2 = do
    let definition = DefValue
          { dvalLocation = Nothing
          , dvalBinder = (ExprValName "MyFun", ty1 :-> TUnit)
          , dvalNoPartyLiterals = HasNoPartyLiterals True
          , dvalIsTest = IsTest False
          , dvalBody = ETmLam (ExprVarName "ignored", ty2) EUnit
          }
    Module
      { moduleName
      , moduleSource = Nothing
      , moduleFeatureFlags = FeatureFlags {forbidPartyLiterals = True}
      , moduleSynonyms = NM.fromList synDefs
      , moduleDataTypes = NM.fromList []
      , moduleValues = NM.fromList [definition]
      , moduleTemplates = NM.empty
      }

typeCheck :: Module -> Either String ()
typeCheck mod = do
  let version = V1 (PointStable 7)
  either (Left . renderPretty) Right $ checkModule (initWorld [] version) version mod

assertStringContains :: String -> Fragment -> IO ()
assertStringContains text (Fragment frag) =
  unless (frag `isInfixOf` text) (assertFailure msg)
  where msg = "expected frag: " ++ frag ++ "\n contained in: " ++ text

newtype Fragment = Fragment String
