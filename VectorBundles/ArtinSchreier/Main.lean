module

public import VectorBundles.ArtinSchreier.ArtinSchreier4
public import VectorBundles.ArtinSchreier.RealClosed

@[expose] public section

theorem artin_schreier_thm (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsAlgClosure F K] : IsAlgClosed F ∨ IsRealClosed F := by
  open IntermediateField IsAlgClosed IsAlgClosure IsIntegral in
  have : IsAlgClosed K := isAlgClosed F
  have ⟨i, hi⟩ := exists_pow_nat_eq (-1 : K) Nat.two_pos; symm at hi
  let F₁ := F⟮i⟯
  have : IsAlgClosure F₁ K := by apply ofAlgebraic F₁ K
  have : ∃ i : F₁, -1 = i^2 := by aesop
  have := finite_algebraic_closure_with_i F₁ K ((isSquare_iff_exists_sq (-1)).mpr this)
  have : F₁ = ⊤ := ext fun x ↦ ⟨fun a ↦ mem_top, fun a ↦
    mem_intermediateField_of_minpoly_splits (Algebra.IsIntegral.isIntegral x) (splits _)⟩
  by_cases hF : IsSquare (-1 : F)
  · left; exact finite_algebraic_closure_with_i F K hF
  · right; exact RealClosed_from_quadratic F K hF ⟨i, ⟨hi, this⟩⟩
