module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsRealClosed.Basic

public import VectorBundles.ArtinSchreier.ArtinSchreier3
public import VectorBundles.ArtinSchreier.RealClosed

@[expose] public section

open IntermediateField

theorem artin_schreier_thm (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsAlgClosure F K] : IsAlgClosed F ∨ IsRealClosed F := by
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  if hF : ∃ j : F, j^2 = -1 then
    left
    apply finite_algebraic_closure_with_i F K hF
  else
    right
    push Not at hF
    obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) Nat.two_pos
    apply RealClosed_from_quadratic F K hF
    use i
    refine ⟨hi, (ext ?_).symm⟩
    intro x
    constructor
    · intro _
      let F₁ := F⟮i⟯
      have : IsIntegral F x := Algebra.IsIntegral.isIntegral x
      apply IsIntegral.mem_intermediateField_of_minpoly_splits this
      have : IsAlgClosure F₁ K := by apply IsAlgClosure.ofAlgebraic F₁ K
      have : IsAlgClosed F₁ := by
        apply finite_algebraic_closure_with_i F₁ K
        aesop
      apply IsAlgClosed.splits
    · exact fun a ↦ mem_top
