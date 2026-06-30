module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

open IntermediateField Polynomial

lemma odd_irreducible_factor {F : Type} [Field F] {f : F[X]} (h : Odd f.natDegree) :
    ∃ g, Irreducible g ∧ g ∣ f ∧ Odd g.natDegree :=
  open Multiset UniqueFactorizationMonoid in
  let S := factors f
  have ⟨g, hg1, hg2⟩ : ∃ g ∈ S, Odd g.natDegree := by
    have h0 := ne_zero_of_natDegree_gt (Odd.pos h); have hp := Associated.symm (factors_prod h0)
    have := (associated_zero_iff_eq_zero f).mp.mt h0
    have : S.prod ≠ 0 := by by_contra; rw [this] at hp; contradiction
    have hd := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hp)
    have h0S := prod_eq_zero.mt this; rw [hd, natDegree_multiset_prod S h0S] at h
    by_contra
    have : 2 ∣ (S.map natDegree).sum := by apply dvd_sum; simp_all [Even.two_dvd]
    grind only [= Nat.odd_iff]
  ⟨g, irreducible_of_factor g hg1, dvd_of_mem_factors hg1, hg2⟩

lemma RealClosed_from_quadratic (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]
    [IsAlgClosure F K] (h1 : ¬IsSquare (-1 : F)) (h2 : ∃ i : K, i^2 = -1 ∧ F⟮i⟯ = ⊤) :
    IsRealClosed F := by
  obtain ⟨i, h2a, h2b⟩ := h2; have hi : i ∉ (algebraMap F K).range := by
    by_contra; obtain ⟨i₀, rfl⟩ := this; have := FaithfulSMul.algebraMap_injective F K
    have : i₀ ^ 2 = -1 := (by apply this; simp_all); grind only [isSquare_iff_exists_sq]
  have h_rank2 : Module.finrank F K = 2 := by open minpoly in
    have h_int := Algebra.IsIntegral.isIntegral i (R := F)
    rw [←finrank_top', ←h2b, adjoin.finrank h_int]; have h := X_pow_add_C_ne_zero two_pos (1 : F)
    have := natDegree_le_of_dvd (dvd_iff (x := i).mpr (by aesop)) h
    grind only [(two_le_natDegree_iff h_int).mpr hi, =natDegree_X_pow_add_C]
  have neg : ∀ x : F, 0 ≠ x → IsSquare x → ¬IsSquare (-x) := by
    intro _ _ hs; by_contra; have := IsSquare.div this hs; grind only
  have h := quadratic_algebraic_closure F K h_rank2
  have hssq : ∀ x : F, IsSumSq x → IsSquare x := by
    apply IsSumSq.rec'; exact IsSquare.zero; intro a b ⟨y, hy⟩ _ hb; by_cases hb0 : 0 = b
    · rw [←hb0, add_zero]; use y
    · rw [hy]; exact Or.resolve_right (h y b) (neg b hb0 hb)
  have := isSemireal_iff_not_isSumSq_neg_one.mpr ((hssq (-1)).mt (neg 1 zero_ne_one IsSquare.one))
  let issquare := h 0; ring_nf at issquare; refine ⟨issquare, ?_⟩; open Nat in
  intro f h; have ⟨w, hg, h_div, h0⟩ := odd_irreducible_factor h
  have hd := Irreducible.natDegree_dvd_finrank hg (pol_splits F K _); rw [h_rank2] at hd
  have h : w.natDegree = 1 := by grind [Prime.eq_one_or_self_of_dvd prime_two _ hd]
  have ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h; exact ⟨x, IsRoot.dvd hx h_div⟩

theorem artin_schreier_thm (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]
  [IsAlgClosure F K] [FiniteDimensional F K] : IsAlgClosed F ∨ IsRealClosed F := by
  open IsAlgClosed IsAlgClosure IsIntegral in
  have : IsAlgClosed K := isAlgClosed F
  have ⟨i, hi⟩ := exists_pow_nat_eq (-1 : K) Nat.two_pos; symm at hi
  have : IsAlgClosure F⟮i⟯ K := by apply ofAlgebraic F⟮i⟯ K
  have := finite_algebraic_closure_with_i F⟮i⟯ K ((isSquare_iff_exists_sq (-1)).mpr (by aesop))
  have : F⟮i⟯ = ⊤ := ext fun x ↦ ⟨fun a ↦ mem_top, fun a ↦
    mem_intermediateField_of_minpoly_splits (Algebra.IsIntegral.isIntegral x) (splits _)⟩
  by_cases hF : IsSquare (-1 : F)
  · left; exact finite_algebraic_closure_with_i F K hF
  · right; exact RealClosed_from_quadratic F K hF ⟨i, ⟨hi.symm, this⟩⟩
