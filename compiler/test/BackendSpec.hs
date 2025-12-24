module BackendSpec (backendTests) where

import Test.Tasty

import Backend.C.Spec (cBackendTests)
import Backend.X86.Spec (x86BackendTests)

-- | All backend tests
backendTests :: TestTree
backendTests = testGroup "Backend" [cBackendTests, x86BackendTests]
