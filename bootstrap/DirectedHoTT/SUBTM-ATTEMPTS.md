# `subTm` over the knot — the attempts log

**Why this file exists.** In `poc/OCP0009` a proof (gap A's `⊢S3s`) took
**51** attempts. What broke it was not attempt 52; it was writing the
first 51 down in a table and reading the column of *why it failed*. Every
one of attempts 45–51 turned out to share a premise nobody had stated:
*`⊢S3` gets built first and converted second.* Dropping the premise closed
it. That record is `bootstrap/poc/OCP0009/GAP-A-ATTEMPTS.md`.

`subTm` is the second place in this project where guesses started
stacking up, so it gets the same treatment. **The rule: an attempt that
is backed out gets a row before the next one is tried.** A failure that
is not written down cannot be compared with the others, and comparing
them is the entire mechanism.

⚠ The useful column is **Why it failed**, not *What was tried*. Two
attempts that fail for the same reason are one attempt.

---

## Step 1 — `⊢extNK` (the extension is type-preserving) ✅ CLOSED

Goal:

    ⊢extNK : Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ sb ∷ SubTy d n →
             Γ ⊢ extNK d n sb ∷ SubTy (nsuc d) (nsuc n)
    SubTy d n = Π (K (pair sVar d)) (K (pair sTm (renTm vs n)))

The body — `⊢lam` over `⊢app (⊢app (⊢extSK …) …) …` — was accepted early.
Everything below is about the *conversions around it*.

| # | Attempt | Result |
|---|---------|--------|
| 1 | `⊢-cast` at the result with a `wk-single` on the codomain | ⚠ moved the goal: the domain mismatch stayed, now under a `subst` |
| 2 | as 1, with the `cong` reshaped to mention the pair | ⚠ same mismatch, different display |
| 3 | `muBwd*` at the result, as used elsewhere in this file | ⚠ `muBwd*` converts an `IMu` payload; the mismatch is *outside* it, in the Π |
| 4 | `⊢conv` at the result with `red→≅ᵀ (predSndPair …)` | ⚠ `predSndPair`'s equation is not the goal's: the goal's is under a Π |

**The shared premise (all four): the body is BUILT first and CONVERTED
second.** So every attempt aimed at the *result* type — where the
offending subterm sits inside a Π domain, a position no `⊢-cast` reaches.
Once stated, the premise is obviously optional.

| # | Attempt | Result |
|---|---------|--------|
| 5 | drop it — convert the **input** `⊢wk dsb` at its source, `⊢conv` with `⟶ᵀ*-Πˡ` | ⚠ closer: domain accepted, **codomain** now mismatched — `vs x != extR vs x` |
| 6 | + `⊢-cast` on the input's codomain by `ren-w` | ⚠ closer still: the reduction's *left* endpoint is under a substitution |
| 7 | + `predSndSub` — `predSndPair` with its right endpoint moved by `wk-single` through a new `⟶*-castᵣ` | ✅ **rc=0** |

**Resolution.** At the input the type is still concrete, and it needs
**two conversions of different kinds** — which is why no single cast was
ever going to work, and why "try another cast" could not have converged:

* the **codomain** differs by a *renaming* → `ren-w`, an `≡` → `⊢-cast`;
* the **domain** differs by a *reduction* → `predSndSub`, a `⟶*` lifted
  through the Π by `⟶ᵀ*-Πˡ` → `⊢conv`.

★ **Both lifting tools already existed** — `ξ-Πˡ` in `Spec/Typing`,
`⟶ᵀ*-Πˡ` in `Metatheory/Injectivity` — proved long before this file. The
four attempts never went looking for them because, under the dropped
premise, a Π-domain congruence had nowhere to be used. **The premise did
not just block the proof; it hid the library.**

### Slips worth not repeating

* Twice the *contexts* were wrong before the *mathematics* was (`w` on
  the endpoint instead of on the pair). Write the statement at the
  context the goal prints, not the one that reads nicely.
* `⟶*-castᵣ` is carrier-generic plumbing that had no home; it is local
  in `Knot/SubMot` pending a second customer. See the two families in
  `HANDOFF-2026-08-27` §"THE PENDING GENERALISATION".

---

## Steps 2–6 — open

Rows get added here as they are tried, **before** the next attempt.

* ⬜ **2.** `⊢sPick`'s `rides` case
* ⬜ **3.** `⊢isubPay`'s two recursive cases
* ⬜ **4.** `⊢isubMethod`
* ⬜ **5.** the tuple at the mask
* ⬜ **6.** `subTmK` + `⊢subTmK`
