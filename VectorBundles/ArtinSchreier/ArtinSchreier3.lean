module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

lemma finite_algebraic_closure_cyclic_quadratic (F : Type) (K : Type) {p : ℕ} [Field F] [Field K]
    [Algebra F K] [IsAlgClosure F K] [IsGalois F K] (hp : Nat.Prime p)
    (hrank : Module.finrank F K = p) : p = 2 ∧ ∃ a : F, ¬IsSquare a ∧ IsSquare (-a) := by
  open Nat Polynomial in
  have hp1 := Prime.pos hp; have := fact_iff.mpr hp
  have := FiniteDimensional.of_finrank_pos (by rw [hrank]; exact hp1)
  have hK : (primitiveRoots p F).Nonempty := by
    have h_char := finite_algebraic_closure_cyclic_prime F K hp hrank
    have := natDegree_pos_iff_degree_pos.mpr (degree_cyclotomic_pos p F hp1)
    rcases divisor_by_finrank F K hrank hp this with ⟨z, hz⟩ | ⟨f, ⟨_, _⟩, hf3⟩
    · have : NeZero (p : F) := ⟨(CharP.charP_iff_prime_eq_zero hp).mpr.mt h_char⟩
      exact ⟨z, (mem_primitiveRoots hp1).mpr (isRoot_cyclotomic_iff.mp hz)⟩
    · have := natDegree_le_of_dvd hf3 (cyclotomic_ne_zero p F)
      rw [natDegree_cyclotomic p F, totient_prime hp] at this; grind
  have ⟨a, h2⟩ : ∃ a : F, Irreducible (Polynomial.X ^ p - Polynomial.C a) := by
    have h := fun hK ↦ (List.TFAE.out (isCyclic_tfae F K hK) 0 1).mp
    have hG := IsGalois.card_aut_eq_finrank F K; rw [hrank] at h hG
    have ⟨a, _, _⟩ := h hK ⟨‹IsGalois F K›, isCyclic_of_prime_card hG⟩; use a
  have hp2 : p = 2 := by
    by_contra
    have h := fun n ↦ X_pow_sub_C_irreducible_iff_of_prime_pow hp this (K := F) (n := n)
    have := (h 2 (by simp)).mpr ((h 1 one_ne_zero).mp (by rw [pow_one]; exact h2))
    have := Irreducible.natDegree_dvd_finrank this (pol_splits F K _)
    have := not_pos_pow_dvd (Prime.one_lt hp) one_lt_two; grind [natDegree_X_pow_sub_C]
  rw [hp2] at h2 hrank; let h := quadratic_algebraic_closure F K hrank 0 a; ring_nf at h
  have ha := nthRoots_two_eq_zero_iff.mp (roots_eq_zero_of_irreducible_of_natDegree_ne_one h2 ?_)
  refine ⟨hp2, ⟨a, ha, ?_⟩⟩; repeat aesop
