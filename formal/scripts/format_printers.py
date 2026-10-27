# The printer induction shared by the proofs that carry a property through
# every printer (plan 0.124 step 4): Canon's sameness under quiet trivia,
# Skeleton's sameness up to the anchors. `BODY` is the text from `ind-opToks`
# to `ind-body`, for a module that defines `Ind`, `ind-pure`, `_⊕ⁱ_`,
# `ind-gn`, `ind-g`, `ind-n`, `ind-paren`, `ind-if`, `ind-word`, `ind-anchor`.
CTORS=[('RVar','x'),('RQualified','x q'),('RResolved','n'),('RApp','f a'),('RLam','x e'),('RLet','x v b'),
 ('RPair','a b'),('RDestruct','s x el y er'),('RUnit',''),('RInt','z'),('RFloat','i fr l'),('RAnnot','e T'),
 ('RBinOp','op a b'),('RNeg','e')]
def P(c,args,pre=''):
    if not args: return c
    return '('+c+' '+' '.join(pre+a for a in args.split())+')'
o=[]; w=o.append
w(r'''  ind-opToks : ∀ cs → Ind (opToks cs)
  ind-opToks []           = ind-pure
  ind-opToks (c ∷ [])     = opTok1′ (opToken c)
    where
      opTok1′ : ∀ m → Ind (opTok1 m)
      opTok1′ (just x) = ind-pure
      opTok1′ nothing  = ind-pure
  ind-opToks (c ∷ d ∷ cs) = opTok1′ (opToken c) ⊕ⁱ ind-pure ⊕ⁱ ind-opToks (d ∷ cs)
    where
      opTok1′ : ∀ m → Ind (opTok1 m)
      opTok1′ (just x) = ind-pure
      opTok1′ nothing  = ind-pure

  ind-name : ∀ x → Ind (name x)
  ind-name x = ind-if (isOperator x) (ind-pure ⊕ⁱ ind-opToks (toList x) ⊕ⁱ ind-pure) (ind-word x)

  ind-grade : ∀ q → Ind (grade q)
  ind-grade Zero = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure
  ind-grade One  = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure
  ind-grade Many = ind-pure ⊕ⁱ ind-pure

  ind-infix : ∀ x → Ind (infixOp x)
  ind-infix x = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure

  mutual
    ind-ty : ∀ l b P → Ind (pty l b P)
    ind-ty l b PUnit = ind-word "Unit"
    ind-ty l b PVoid = ind-word "Void"
    ind-ty l b PInt = ind-word "Int"
    ind-ty l b PFloat = ind-word "Float"
    ind-ty l b (PTVar x) = ind-word x
    ind-ty l b (A P⇒[ q ] B) = ind-paren (0 <ᵇ l) (ind-ty 1 true A ⊕ⁱ ind-grade q ⊕ⁱ ind-pure ⊕ⁱ ind-ty 0 (b ∨ (0 <ᵇ l)) B)
    ind-ty l b (A P+ B) = ind-paren (1 <ᵇ l) (ind-ty 1 false A ⊕ⁱ ind-infix _ ⊕ⁱ ind-ty 2 (b ∨ (1 <ᵇ l)) B)
    ind-ty l b (A P* B) = ind-paren (2 <ᵇ l) (ind-ty 2 false A ⊕ⁱ ind-infix _ ⊕ⁱ ind-ty 3 (b ∨ (2 <ᵇ l)) B)
    ind-ty l b (PEff A B) = ind-paren (3 <ᵇ l) (ind-word "Eff" ⊕ⁱ ind-pure ⊕ⁱ ind-ty 3 false A ⊕ⁱ ind-pure ⊕ⁱ ind-ty 3 false B)
    ind-ty l b (PAct A B) = ind-paren (3 <ᵇ l) (ind-word "Act" ⊕ⁱ ind-pure ⊕ⁱ ind-ty 3 false A ⊕ⁱ ind-pure ⊕ⁱ ind-ty 3 false B)
    ind-ty l b (Pμ F) = ind-paren (not b) (ind-word "Mu" ⊕ⁱ ind-pure ⊕ⁱ ind-arg F)
    ind-ty l b (Pν F pureᶠ) = ind-paren (not b) (ind-word "Nu" ⊕ⁱ ind-pure ⊕ⁱ ind-arg F)
    ind-ty l b (Pν F actᶠ) =
      ind-paren (not b) (ind-word "Nu" ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-word "Act" ⊕ⁱ ind-pure ⊕ⁱ ind-fun 0 F ⊕ⁱ ind-pure)

    ind-arg : ∀ F → Ind (pfunArg F)
    ind-arg PId = ind-word "Id"
    ind-arg (PK A) = ind-pure ⊕ⁱ ind-fun 0 (PK A) ⊕ⁱ ind-pure
    ind-arg (F P⊕ G) = ind-pure ⊕ⁱ ind-fun 0 (F P⊕ G) ⊕ⁱ ind-pure
    ind-arg (F P⊗ G) = ind-pure ⊕ⁱ ind-fun 0 (F P⊗ G) ⊕ⁱ ind-pure

    ind-fun : ∀ l F → Ind (pfun l F)
    ind-fun l PId = ind-word "Id"
    ind-fun l (PK A) = ind-paren (1 <ᵇ l) (ind-word "K" ⊕ⁱ ind-pure ⊕ⁱ ind-ty 3 false A)
    ind-fun l (F P⊕ G) = ind-paren (0 <ᵇ l) (ind-fun 0 F ⊕ⁱ ind-infix _ ⊕ⁱ ind-fun 1 G)
    ind-fun l (F P⊗ G) = ind-paren (1 <ᵇ l) (ind-fun 1 F ⊕ⁱ ind-infix _ ⊕ⁱ ind-fun 2 G)

  mutual
    ind-ex : ∀ l wh e → Ind (pex l wh e)
    ind-ex l wh (RVar x) = ind-name x
    ind-ex l wh (RQualified x q) = ind-word x ⊕ⁱ ind-pure ⊕ⁱ ind-word q
    ind-ex l wh (RResolved (canonical xs)) = ind-dotted xs
    ind-ex l wh (RApp f a) = ind-comp l (isCompose (headOf f)) f a
    ind-ex l wh (RLam x e) = ind-paren (not wh) (ind-g (ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-lam e))
    ind-ex l wh (RLet x v b) = ind-paren (not wh) (ind-g (ind-let x v b))
    ind-ex l wh (RPair a b) =
      ind-gn (ind-pure ⊕ⁱ ind-ex 0 true a ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true b ⊕ⁱ ind-pure)
    ind-ex l wh (RDestruct s x el y er) =
      ind-paren (not wh) (ind-g (ind-word "destruct" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true s ⊕ⁱ ind-pure ⊕ⁱ ind-word "of"
        ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-word "Left" ⊕ⁱ ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-infix _
            ⊕ⁱ ind-ex 0 true el ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-word "Right" ⊕ⁱ ind-pure ⊕ⁱ ind-word y
            ⊕ⁱ ind-infix _ ⊕ⁱ ind-ex 0 true er ⊕ⁱ ind-pure ⊕ⁱ ind-pure)))
    ind-ex l wh RUnit = ind-pure ⊕ⁱ ind-pure
    ind-ex l wh (RInt z) = ind-anchor (TInt z)
    ind-ex l wh (RFloat i f n) = ind-anchor (TFloat i f n)
    ind-ex l wh (RAnnot e T) = ind-pure ⊕ⁱ ind-ex 0 true e ⊕ⁱ ind-infix _ ⊕ⁱ ind-ty 0 true (toPoly T) ⊕ⁱ ind-pure
    ind-ex l wh (RBinOp op a b) = ind-gn (ind-paren (opLevel op <ᵇ l) (ind-bin (opLevel op) op a b))
    ind-ex l wh (RNeg e) = ind-paren (4 <ᵇ l) (ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ex 4 false e)

    ind-dotted : ∀ xs → Ind (dotted xs)
    ind-dotted [] = ind-pure
    ind-dotted (x ∷ []) = ind-word x
    ind-dotted (x ∷ y ∷ ys) = ind-word x ⊕ⁱ ind-pure ⊕ⁱ ind-dotted (y ∷ ys)

    ind-comp : ∀ l b f a → Ind (pcomp l b f a)''')
for c,args in CTORS:
    if c=='RApp':
        w('    ind-comp l true (RApp c g) h = ind-compose l g h')
    else:
        w(f'    ind-comp l true {P(c,args,"u")} a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine {P(c,args,"u")} ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))')
w('''    ind-comp l false f a = ind-gn (ind-paren (5 <ᵇ l) (ind-spine f ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a))

    ind-compose : ∀ l g h → Ind (pcompose l g h)
    ind-compose l g h = ind-gn (ind-paren (0 <ᵇ l) (ind-chain g ⊕ⁱ (ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure) ⊕ⁱ ind-ex 1 false h))

    ind-chain : ∀ g → Ind (pchainC g)
    ind-chain (RApp f h) = ind-chain′ (isCompose (headOf f)) f h''')
for c,args in CTORS:
    if c=='RApp': continue
    w(f'    ind-chain {P(c,args)} = ind-ex 1 false {P(c,args)}')
w('''
    ind-chain′ : ∀ b f h → Ind (pchainC′ b f h)''')
for c,args in CTORS:
    if c=='RApp':
        w('    ind-chain′ true (RApp c g) h = ind-chain g ⊕ⁱ (ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure) ⊕ⁱ ind-ex 1 false h')
    else:
        w(f'    ind-chain′ true {P(c,args,"u")} h = ind-comp 0 false {P(c,args,"u")} h')
w('''    ind-chain′ false f h = ind-comp 0 false f h

    ind-bin : ∀ lv op a b → Ind (pbin lv op a b)
    ind-bin lv op a b = ind-left lv a ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ex (suc lv) false b

    ind-left : ∀ lv a → Ind (pleft lv a)
    ind-left lv (RBinOp op x y) = ind-if ((lv ≡ᵇ opLevel op) ∧ (1 <ᵇ lv)) (ind-bin lv op x y) (ind-ex (leftLevel lv) false (RBinOp op x y))''')
for c,args in CTORS:
    if c=='RBinOp': continue
    w(f'    ind-left lv {P(c,args)} = ind-ex (leftLevel lv) false {P(c,args)}')
w('''
    ind-spine : ∀ f → Ind (pspine f)
    ind-spine (RApp f a) = ind-spine′ (isCompose (headOf f)) f a''')
for c,args in CTORS:
    if c=='RApp': continue
    w(f'    ind-spine {P(c,args)} = ind-ex 6 false {P(c,args)}')
w('''
    ind-spine′ : ∀ b f a → Ind (pspine′ b f a)''')
for c,args in CTORS:
    if c=='RApp':
        w('    ind-spine′ true (RApp c g) h = ind-compose 6 g h')
    else:
        w(f'    ind-spine′ true {P(c,args,"u")} a = ind-spine {P(c,args,"u")} ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a')
w('''    ind-spine′ false f a = ind-spine f ⊕ⁱ ind-pure ⊕ⁱ ind-ex 6 false a

    ind-lam : ∀ e → Ind (plam′ e)
    ind-lam (RLam y e) = ind-pure ⊕ⁱ ind-word y ⊕ⁱ ind-lam e''')
for c,args in CTORS:
    if c=='RLam': continue
    w(f'    ind-lam {P(c,args)} = ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-n (ind-pure ⊕ⁱ ind-ex 0 true {P(c,args)})')
w('''
    ind-lhead : ∀ x v → Ind (lhead x v)
    ind-lhead x v = ind-word "let" ⊕ⁱ ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-gn (ind-pure ⊕ⁱ ind-ex 0 true v)

    ind-let : ∀ x v b → Ind (plet′ x v b)
    ind-let x v (RLet y v′ c) = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-let y v′ c''')
for c,args in CTORS:
    if c=='RLet': continue
    w(f'    ind-let x v {P(c,args,"b")} = ind-lhead x v ⊕ⁱ ind-pure ⊕ⁱ ind-word "in" ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true {P(c,args,"b")}')
w('''
  private
    ind-path : ∀ p → Ind (path p)
    ind-path [] = ind-pure
    ind-path (x ∷ []) = ind-word x
    ind-path (x ∷ y ∷ ys) = ind-word x ⊕ⁱ ind-pure ⊕ⁱ ind-path (y ∷ ys)

    ind-spaced : ∀ ps → Ind (spaced ps)
    ind-spaced [] = ind-pure
    ind-spaced (x ∷ xs) = ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-spaced xs

  -- | A declaration prints alike.
  ind-body : ∀ d → Ind (pbody d)
  ind-body (DImport (mkImport p nothing)) = ind-word "import" ⊕ⁱ ind-pure ⊕ⁱ ind-path p
  ind-body (DImport (mkImport p (just a))) =
    ind-word "import" ⊕ⁱ ind-pure ⊕ⁱ ind-path p ⊕ⁱ ind-pure ⊕ⁱ ind-word "as" ⊕ⁱ ind-pure ⊕ⁱ ind-word a
  ind-body (DTypeAlias x ps A) =
    ind-word "type" ⊕ⁱ ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-spaced ps ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ty 0 true A
  ind-body (DSignature x A) =
    ind-word "signature" ⊕ⁱ ind-pure ⊕ⁱ ind-word x ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ty 0 true A
  ind-body (DTypeSig x A) = ind-name x ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ty 0 true A
  ind-body (DFunDef x e) =
    ind-name x ⊕ⁱ ind-spaced (proj₁ (lams e)) ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-pure ⊕ⁱ ind-ex 0 true (proj₂ (lams e))
''')
BODY='\n'.join(o)
