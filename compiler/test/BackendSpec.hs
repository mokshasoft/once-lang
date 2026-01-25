module BackendSpec (backendTests) where

import Test.Tasty

import Backend.C.Spec (cBackendTests)

-- | All backend tests
backendTests :: TestTree
backendTests = testGroup "Backend" [cBackendTests]
