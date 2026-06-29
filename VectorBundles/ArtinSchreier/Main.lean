module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

open IntermediateField Polynomial

lemma odd_irreducible_factor {F : Type} [Field F] {f : F[X]} (h : Odd f.natDegree) :
  ∃ g, Irreducible g ∧ g ∣ f ∧ Odd g.natDegree :=
  open UniqueFactorizationMonoid in
  let S := factors f
  have ⟨g, hg1, hg2⟩ : ∃ g ∈ S, Odd g.natDegree := by
    have h0 := ne_zero_of_natDegree_gt (Odd.pos h); have hp := Associated.symm (factors_prod h0)
    have := (associated_zero_iff_eq_zero f).mp.mt h0
    have : S.prod ≠ 0 := by by_contra; rw [this] at hp; contradiction
    have hd := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hp)
    have h0S := Multiset.prod_eq_zero.mt this; rw [hd, natDegree_multiset_prod S h0S] at h
    by_contra
    have : 2 ∣ (S.map natDegree).sum := by apply Multiset.dvd_sum; simp_all [Even.two_dvd]
    grind only [= Nat.odd_iff]
  ⟨g, irreducible_of_factor g hg1, dvd_of_mem_factors hg1, hg2⟩

lemma RealClosed_from_quadratic (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]
    [IsAlgClosure F K] (h1 : ¬IsSquare (-1 : F)) (h2 : ∃ i : K, i^2 = -1 ∧ F⟮i⟯ = ⊤) :
    IsRealClosed F := by
  obtain ⟨i, h2a, h2b⟩ := h2
  let iota := algebraMap F K; have hi : i ∉ iota.range := by
    by_contra; obtain ⟨i₀, h⟩ := this; have := FaithfulSMul.algebraMap_injective F K
    have : i₀^2 = -1 := (by aesop); grind only [isSquare_iff_exists_sq]
  have h_int := Algebra.IsIntegral.isIntegral i (R := F)
  have h_rank2 : (minpoly F i).natDegree = 2 := by open minpoly in
    have ha : aeval i (X ^ 2 + C (1 : F)) = 0 := by aesop
    have := natDegree_le_of_dvd (dvd_iff.mpr ha) (X_pow_add_C_ne_zero two_pos 1)
    have := (two_le_natDegree_iff h_int).mpr hi; grind only [=natDegree_X_pow_add_C]
  rw [←adjoin.finrank h_int, h2b, finrank_top'] at h_rank2
  have odd_deg : ∀ {f : F[X]}, Odd f.natDegree → ∃ x, f.IsRoot x := by
    intro f h; have ⟨_, hg, h_div, _⟩ := odd_irreducible_factor h
    rcases divisor_by_finrank F K h_rank2 Nat.prime_two (Irreducible.natDegree_pos hg)
      with ⟨x, hx⟩ | ⟨w, ⟨_, _⟩, hd3⟩
    · exact ⟨x, IsRoot.dvd hx h_div⟩
    · have := not_isUnit_of_natDegree_pos w (by grind)
      have := (Irreducible.isUnit_iff_not_associated_of_dvd hg hd3).mpr.mt this
      grind [natDegree_eq_of_degree_eq, degree_eq_degree_of_associated]
  have neg : ∀ x : F, 0 ≠ x → IsSquare x → ¬IsSquare (-x) := by
    intro x hx hs; by_contra; have := IsSquare.div this hs
    rw [neg_div_self hx.symm] at this; contradiction
  have h := quadratic_algebraic_closure F K h_rank2
  have hssq : ∀ x : F, IsSumSq x → IsSquare x := by
    apply IsSumSq.rec'; exact IsSquare.zero
    intro a b ⟨y, hy⟩ _ hb; by_cases hb0 : 0 = b
    · rw [←hb0, add_zero]; use y
    · rw [hy]; exact Or.resolve_right (h y b) (neg b hb0 hb)
  have := isSemireal_iff_not_isSumSq_neg_one.mpr ((hssq (-1)).mt (neg 1 zero_ne_one IsSquare.one))
  let issquare := h 0; ring_nf at issquare; exact ⟨issquare, odd_deg⟩

theorem artin_schreier_thm (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]
  [IsAlgClosure F K] [FiniteDimensional F K] : IsAlgClosed F ∨ IsRealClosed F := by
  open IntermediateField IsAlgClosed IsAlgClosure IsIntegral in
  have : IsAlgClosed K := isAlgClosed F
  have ⟨i, hi⟩ := exists_pow_nat_eq (-1 : K) Nat.two_pos; symm at hi
  let F₁ := F⟮i⟯; have : IsAlgClosure F₁ K := by apply ofAlgebraic F₁ K
  have := finite_algebraic_closure_with_i F₁ K ((isSquare_iff_exists_sq (-1)).mpr (by aesop))
  have : F₁ = ⊤ := ext fun x ↦ ⟨fun a ↦ mem_top, fun a ↦
    mem_intermediateField_of_minpoly_splits (Algebra.IsIntegral.isIntegral x) (splits _)⟩
  by_cases hF : IsSquare (-1 : F)
  · left; exact finite_algebraic_closure_with_i F K hF
  · right; exact RealClosed_from_quadratic F K hF ⟨i, ⟨hi.symm, this⟩⟩
