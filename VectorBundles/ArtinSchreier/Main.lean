module

public import VectorBundles.ArtinSchreier.ArtinSchreier4
public import VectorBundles.ArtinSchreier.RealClosed

@[expose] public section

theorem artin_schreier_thm (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsAlgClosure F K] : IsAlgClosed F ∨ IsRealClosed F := by
  open IntermediateField IsAlgClosed IsAlgClosure in
  have : IsAlgClosed K := isAlgClosed F
  obtain ⟨i, hi⟩ := exists_pow_nat_eq (-1 : K) Nat.two_pos
  symm at hi
  let F₁ := F⟮i⟯
  have : IsAlgClosure F₁ K := by apply ofAlgebraic F₁ K
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : F₁, i₁ = i := CanLift.prf i (mem_adjoin_simple_self F i)
  have : ∃ i : F₁, -1 = i^2 := by aesop
  have := finite_algebraic_closure_with_i F₁ K this
  have : F₁ = ⊤ := by
    apply ext
    intro x
    refine ⟨fun a ↦ mem_top, ?_⟩
    intro _
    apply IsIntegral.mem_intermediateField_of_minpoly_splits (Algebra.IsIntegral.isIntegral x)
    apply splits
  if hF : ∃ j : F, -1 = j^2 then
    left
    apply finite_algebraic_closure_with_i F K hF
  else
    right
    push Not at hF
    apply RealClosed_from_quadratic F K hF
    use i
