{-# OPTIONS --safe #-}
module tmp.TermProbe where
open import DirectedHoTT.Spec.Syntax
import DirectedHoTT.Spec.Bind as G
private variable Γ : Cx
-- (a) the scope pinned on both sides
f4 : RTy Γ → RTy Γ
f4 (Hom (DIh {Γ} D M C p) t u) = Hom (f4 (DIh {Γ} D M C p)) t u
f4 (DIh D M C p) = DIh D (f4 M) C p
f4 A = A
-- (b) a rebuilt subterm with NO binder field (El has one depth-0 field)
f5 : RTy Γ → RTy Γ
f5 (Hom (El e) t u) = Hom (f5 (El e)) t u
f5 (El e) = El e
f5 A = A
-- (c) a rebuilt subterm with a binder field (Π), no two-binder field
f6 : RTy Γ → RTy Γ
f6 (Hom (Π A B) t u) = Hom (f6 (Π A B)) t u
f6 (Π A B) = Π (f6 A) (f6 B)
f6 A = A
