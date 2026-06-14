module

public import VectorBundles.ArtinSchreier.ArtinSchreier3
public import VectorBundles.ArtinSchreier.RealClosed

@[expose] public section

open IntermediateField

theorem artin_schreier_thm (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsAlgClosure F K] : IsAlgClosed F ∨ IsRealClosed F := by
  if hF : ∃ j : F, -1 = j^2 then
    left
    apply finite_algebraic_closure_with_i F K hF
  else
    right
    push Not at hF
    have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
    apply RealClosed_from_quadratic F K hF
    obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) Nat.two_pos
    use i
    symm at hi
    refine ⟨hi, (ext ?_).symm⟩
    intro x
    let F₁ := F⟮i⟯
    have : IsAlgClosure F₁ K := by apply IsAlgClosure.ofAlgebraic F₁ K
    have : ∃ i : F₁, -1 = i^2 := by aesop
    have := finite_algebraic_closure_with_i F₁ K this
    refine ⟨?_, fun a ↦ mem_top⟩
    intro _
    apply IsIntegral.mem_intermediateField_of_minpoly_splits (Algebra.IsIntegral.isIntegral x)
    apply IsAlgClosed.splits
