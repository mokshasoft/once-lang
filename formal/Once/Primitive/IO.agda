------------------------------------------------------------------------
-- Once.Primitive.IO
--
-- Axiomatic specification of I/O primitives.
--
-- This module provides an abstract model of I/O effects, independent
-- of any particular implementation.
--
-- I/O is modeled as operations on an abstract "World" state that
-- captures the external environment (files, console, network, etc.).
--
-- KEY INSIGHT: I/O is orthogonal to the type system. These axioms
-- constrain runtime behavior without affecting type checking.
--
------------------------------------------------------------------------

module Once.Primitive.IO where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; Dec)

------------------------------------------------------------------------
-- Abstract Types
------------------------------------------------------------------------

-- | Abstract world state
--
-- The world captures all external state: file system, console buffers,
-- network connections, random state, time, etc.
--
-- We don't expose its structure - only axioms about how I/O affects it.
postulate
  World : Set

-- | Initial world (program start)
postulate
  initialWorld : World

-- | File descriptor type
postulate
  FileDesc : Set

-- | Standard file descriptors
postulate
  stdin  : FileDesc
  stdout : FileDesc
  stderr : FileDesc

-- | Byte sequence (for buffers)
Bytes : Set
Bytes = List ℕ  -- Each ℕ is 0-255

------------------------------------------------------------------------
-- Console Output
--
-- print, println, err, errln, putc, flush
------------------------------------------------------------------------

-- | Write bytes to stdout
postulate
  writeStdout : Bytes → World → World

-- | Write bytes to stderr
postulate
  writeStderr : Bytes → World → World

-- | Flush output buffers
postulate
  flushOutput : World → World

-- | Output ordering: writes to same stream are ordered
-- (Captured implicitly by World threading)

------------------------------------------------------------------------
-- Console Input
--
-- getc, getline
------------------------------------------------------------------------

-- | Read result: either a byte or EOF
data ReadResult : Set where
  byte : ℕ → ReadResult      -- 0-255
  eof  : ReadResult

-- | Read one byte from stdin
postulate
  readByte : World → ReadResult × World

-- | EOF is sticky: once EOF, always EOF
postulate
  eof-sticky : ∀ w →
    let (r , w') = readByte w
    in r ≡ eof →
    let (r' , _) = readByte w'
    in r' ≡ eof

------------------------------------------------------------------------
-- File Operations
--
-- open, read, write, close, stat
------------------------------------------------------------------------

-- | Open flags (simplified)
data OpenMode : Set where
  readOnly  : OpenMode
  writeOnly : OpenMode
  readWrite : OpenMode
  create    : OpenMode

-- | Open result
data OpenResult : Set where
  opened : FileDesc → OpenResult
  error  : ℕ → OpenResult      -- Error code

-- | Open a file
postulate
  openFile : String → OpenMode → World → OpenResult × World

-- | Close a file descriptor
postulate
  closeFile : FileDesc → World → ℕ × World  -- Returns 0 on success

-- | Read from file descriptor
postulate
  readFile : FileDesc → ℕ → World → (Bytes × ℕ) × World
  -- Returns (bytes read, count) - count ≤ requested

-- | Write to file descriptor
postulate
  writeFile : FileDesc → Bytes → World → ℕ × World
  -- Returns bytes written

-- | Read axiom: never reads more than requested
postulate
  read-bounded : ∀ fd n w →
    let ((bs , count) , _) = readFile fd n w
    in count ≤ n

-- | Read axiom: count matches actual bytes
postulate
  read-count-correct : ∀ fd n w →
    let ((bs , count) , _) = readFile fd n w
    in length bs ≡ count

------------------------------------------------------------------------
-- File System Operations
------------------------------------------------------------------------

-- | File existence check result
postulate
  fileExists : String → World → Maybe ℕ × World
  -- Returns just size if exists, nothing if not

-- | Get file size
postulate
  fileSize : String → World → Maybe ℕ × World

------------------------------------------------------------------------
-- Non-determinism and External Effects
------------------------------------------------------------------------

-- | The world is not fully deterministic
--
-- External events (user input, network, time) introduce non-determinism.
-- We model this by NOT postulating determinism for most operations.
--
-- However, pure computations between I/O points are deterministic.

-- | Time operations
postulate
  getTime : World → ℕ × World  -- Returns Unix timestamp

-- | Time is monotonic
postulate
  time-monotonic : ∀ w →
    let (t₁ , w₁) = getTime w
        (t₂ , _)  = getTime w₁
    in t₁ ≤ t₂

------------------------------------------------------------------------
-- World Axioms
------------------------------------------------------------------------

-- | Different I/O operations produce different worlds
-- (The world always changes, even if the "visible" effect is the same)
--
-- This is important for reasoning: we can't assume w ≡ w' just because
-- an operation "did nothing visible".

-- | Standard streams are distinct
postulate
  stdin≢stdout  : stdin ≢ stdout
  stdin≢stderr  : stdin ≢ stderr
  stdout≢stderr : stdout ≢ stderr

------------------------------------------------------------------------
-- Summary of Trusted Axioms
------------------------------------------------------------------------

-- This module introduces the following postulates:
--
-- Types:
--   World, initialWorld, FileDesc, stdin, stdout, stderr
--
-- Console:
--   writeStdout, writeStderr, flushOutput, readByte, eof-sticky
--
-- Files:
--   openFile, closeFile, readFile, writeFile,
--   read-bounded, read-count-correct, fileExists, fileSize
--
-- Time:
--   getTime, time-monotonic
--
-- These axioms are validated by the implementations in
-- Strata/Interpretations/Linux/File.* and syscalls.*.
--

