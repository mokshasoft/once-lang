# INPUT — data types and structures: what the language side asks of this kernel

Written 2026-11-04, from plan 0.147 ("Named data types and lawful structures, with no new mathematics";
numbered 0.140 on its first branch; branch `0.147-data-and-structures` of the compiler repo,
`plans/0.147-data-types-and-structures.md`). That plan
designs `data`, `codata`, `record`, `abstract` and lawful structures for Once BEFORE dependent types, and
postpones to dependent types whatever they solve naturally. This file lists what those decisions assume of
this kernel, so the DT work can take them in. Nothing here is decided for the kernel: these are requests
and findings, to be weighed against `ROADMAP.md`.

## 1. Decisions on the language side (plan 0.147, user, 2026-11-03/04)

- **`data` / `codata`** are the keywords. `data` is declared by constructors (an algebra into the
  carrier); `codata` by destructors (a coalgebra out of it), with copattern corecursion:

  ```
  data   List a   = Nil | Cons a (List a)
  codata Stream a = head : a | tail : Stream a
  head (nats n) = n
  tail (nats n) = nats (n + 1)
  ```

- **Data types are NOMINAL**: a declaration makes a new type whose meaning is its representation's
  (`⟦T⟧ = μ F_T`); only the typing changes.
- **Types are formed relative to a signature of declarations** (Coq/Agda/Lean style). A declaration enters
  the signature with its type former, constructors and fold.
- **One `abstract` attribute, for every declaration**, marked at the declaration (OCP-0010 R1):
  `abstract data T` hides constructors and fold outside the module; `abstract type Celsius = Int` is
  `newtype`; `abstract f` means f's body does not unfold in conversion outside the module.
- **`record`**: a nominal product defined by its projections (η holds). Under dependent types a record
  with a type field is the Σ-package for theories, models and abstract types.
- **Self-reference is surface sugar**: a definition may call itself on an immediate subterm (elaborated to
  cata/para) or in a guarded copattern position (elaborated to ana). The core has no self-reference.
  Rule: matching puts a "call slot" for each recursive-position variable into the context; a call is
  legal only on a slotted variable. Nested patterns are in the first version.
- **Structures are explicit records** (no instance search, OCP-0010 R7). No unlawful structures: until
  dependent types, laws are proved off-line in Agda (or postulated by name), as an Interpretation's
  contracts are; the optimizer does not use them. With dependent types the laws are proved in Once.
- **Postponed to dependent types**: GADTs and indexed families, nested types (polymorphic recursion),
  function-typed recursive fields (W-types), laws in the language and hand-written user models, higher
  kinds, intensional type analysis, refinement types.

Added 2026-11-06, when the plan's decisions were completed:

- **`match`** replaces positional `destruct`; `inl`/`inr` are the constructors of `+`.
- **Nested positive occurrences** (`data Rose a = Node a (List (Rose a))`) and **mutual `data`** are in
  the pre-DT language: a field may apply a declared, strictly positive type to the recursive position
  (variance recorded per declaration); mutual declarations elaborate to nested μ by Bekić's lemma.
  Recursion through a nested position is `map f ts` (a call slot) or a helper in a mutual function group.
- **Structured types**: `==` is the diagonal's classifier, automatic wherever equality is decidable (not on
  functions, codata, or abstract types outside their module). Structure is declared with the type and an
  operator symbol, bound to exactly one theory, resolves through its operand type's declaration: one
  candidate, coherent by construction, no search. **A kind names a theory** (`∀(a : Ord)`), `Eq` the
  automatic one. User types declare only derived structure (transport along the iso, products of models,
  lexicographic order) until dependent types.
- **Float**: `==` is identity, `<` is IEEE `totalOrder`, IEEE arithmetic and comparison are `+. *. ==. <.`
  …, Float's theory is RoundedField (field operations conjugated by rounding, the standard error bound),
  NaN results canonical.

## 2. What this asks of the kernel

### 2.1 Opaque signature entries (needed for nominal types and `abstract`)

`Spec/Reduction.agda`'s `δref` unfolds every entry unconditionally. So two `data` entries with equal
descriptions are convertible: data types here are structural. The language decisions map onto **opaque
entries**:

| Language | Kernel |
|---|---|
| nominal `data T` | the type entry for `T` never unfolds in conversion (`T` is a name); constructors and fold are separate entries whose types mention `T` |
| `abstract data T` | additionally, those constructor and fold entries are invisible outside the declaring module's segment |
| `abstract f` | `f`'s entry does not unfold outside its segment (Agda `abstract`/`opaque`, Lean `irreducible`) |

Mechanism to evaluate: a δ side condition per entry, scoped by signature segment (D081 already makes a
module a segment). `δref`'s existing side condition (`d <ˢ size`) keeps reduction monotone under signature
extension; opacity scoped by segment should keep that property (an opaque entry is stuck outside its
segment exactly as an out-of-range name is stuck everywhere). The metatheory (SR, confluence, canonicity)
must survive stuck opaque references: they behave like neutral variables of the declared type.

Side benefit: opacity is also the type-checking cost tool (PERF.md, LESSONS.md: `abstract` against
substitution towers; `SD` opaque in PLAN-REF), now available in the object language.

### 2.2 Data declarations elaborate to `IMu` over `Desc`

The pre-DT language extends the compiler Spec's functor grammar (`Fun ::= K A | Id | F ⊕ G | F ⊗ G`)
with composition / parameterised μ, so that `data Rose a = Node a (List (Rose a))` and syntax trees with
lists of children are expressible (plan 0.147 §3.4). Request: that extension is designed as a **fragment
of `Desc`**, so a pre-DT `data` declaration is a `Desc` without indices and dependent types extend it
rather than replace it. Open on this side: does `Desc` here support a field whose code is `⌜IMu⌝` of
another description applied to the recursive position (nested μ, rose trees), and in what form?

Decided since (2026-11-06): nested positive occurrences are in the pre-DT language, and mutual `data`
declarations elaborate to nested μ by Bekić's lemma, so mutual families need no separate former if
`Desc` supports the nesting. Variance per declared parameter is recorded on the language side, as
`Spec/Variance` does here.

Constructor tags: the kernel uses one `Fin n` tag; the compiler Spec has binary `+` only, so an
n-constructor `data` is nested sums there. Same meaning; a layout matter (one tag word vs one per level).

### 2.3 Pattern matching must elaborate to eliminators, and K-free

The surface elaborates clauses (nested patterns, call slots) to `fold`/`para`. Under dependent types the
same clauses meet indexed families, and dependent pattern matching needs unification of indices
(Goguen–McBride–McKinna, "Eliminating dependent pattern matching"). Since this kernel has `Id` and a
directed `Hom` and aims at HoTT-compatibility, the elaboration must not assume axiom K: **pattern
matching without K** (Cockx–Devriese–Piessens). Worth recording as a constraint on the elaborator
(`Algorithm/Elab`) before indexed families are matched on in surface syntax.

### 2.4 Codata stays out of conversion

Consistent with OCP-0009 §2 and the kernel (no codata former): `codata` declarations and copattern
corecursion live in the runtime fragment, never as type-level computation. Nothing to change; recorded so
the two sides do not drift.

### 2.5 Records as Σ-packages: theories, models, abstract types

Under dependent types:
- a **theory** (Monoid, Ord, Monad) is a record type with operation fields and law fields;
- the **law fields are at quantity 0** (R5): checked, erased, no run-time cost;
- a **model** is a record value; a model that cannot prove its laws states a named postulate, which is
  listed in the trust surface (`Trust.agda`'s discipline: listed and checked);
- an **abstract type** is an existential package (Mitchell–Plotkin): the type, its operations and its
  laws, i.e. a model of a theory. So `abstract` (2.1) and lawful structures become one mechanism.

Needs: records (or Σ) with a type field, i.e. a universe in the record's field (the kernel has `U`); η for
records; QTT grades on fields (R5).

### 2.6 Laws as directed paths (to evaluate)

`Hom t u = t ⟶* u` is an oriented equation. A structure's law stated as a `Hom`
(`bind (return a) f ⟶ f a`) is a rewrite with an in-language certificate, which the optimizer could
apply. Plan 0.147 §3.5 item 7 keeps the optimizer away from structure laws until dependent types and names this
as the candidate "proper solution". Question for this kernel: can a user-stated `Hom` between two
closed programs serve as an optimizer rewrite certificate, and what does R6 (converging with the compiler
core) need for that?

### 2.6b Theories as kinds become records over the universe

On the language side a kind names a theory (`∀(a : Ord). …`) and a type's declaration carries its
models. Under dependent types: a theory-kind is a record type over `U` (operation fields, law fields at
quantity 0); a structured type is a Σ-package (the type with its models); resolution by the operand's
type is a projection from the type's own signature entry, so it needs no search. The surface stays.

### 2.7 No instance search in the elaborator

OCP-0010 R7 holds on this side too: explicit structures, no instance arguments. If implicit resolution is
ever added (not planned, plan 0.147 §4; "canonical models": one per theory and carrier, declared with either, no
orphans), it needs a coherence theorem so the meaning stays a function of the judgment. Recorded so the
elaborator does not grow instance search independently.

## 3. Where to read more

- Compiler repo, branch `0.147-data-and-structures`: `plans/0.147-data-types-and-structures.md` (§3
  decisions, §4 postponed to dependent types, §5 the reading of this kernel this file summarises).
- Parametricity of polymorphic definitions: compiler repo master, D371.
- OCP-0009 Rung 4 (indexed families), Rung 5 (erasure).
