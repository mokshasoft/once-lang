module BackendSpec (backendTests) where

import Test.Tasty

import Backend.C.Spec (cBackendTests)

-- | All backend tests
-- Currently only C backend is implemented
backendTests :: TestTree
backendTests = testGroup "Backend" [cBackendTests]
