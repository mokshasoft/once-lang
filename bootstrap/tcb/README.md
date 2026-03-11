# Trusted Computing Base

**EVERYTHING IN THIS DIRECTORY MUST BE HUMAN-VERIFIED.**

This is the minimal trusted code for Once verification:

| File | Lines | Purpose |
|------|-------|---------|
| `scheme.c` | ~200 | Minimal Scheme interpreter |
| `verifier.scm` | ~12 | Trace verification logic |

## Verification Checklist

Before trusting this TCB:

- [ ] Read every line of `scheme.c`
- [ ] Verify it implements S-expression parsing correctly
- [ ] Verify it implements `equal?`, `car`, `cdr`, `cons` correctly
- [ ] Read every line of `verifier.scm`
- [ ] Verify each rule matches the categorical law it implements
- [ ] Cross-check with multiple reviewers
- [ ] Optionally: implement independently and compare

## Building

```bash
make
```

This produces `./scheme` - the minimal interpreter.

## Testing the Verifier

```bash
./scheme verifier.scm < test-trace.scm
```

## Why So Small?

The smaller the TCB, the easier to verify:
- 200 lines can be read in an hour
- Each line can be reasoned about
- Multiple independent implementations can cross-check
- A mathematician can verify the laws match category theory
