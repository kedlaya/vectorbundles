module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import VectorBundles.ArtinSchreier.ArtinSchreier

@[expose] public section

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] (h : IsSquare (-1 : F))

/- A field admitting a finite purely inseparable extension which is algebraically closed
   is perfect (and hence itself algebraically closed). -/
lemma finite_inseparable_algebraic_closure [IsPurelyInseparable F K] : PerfectField F := by
  open CharP FaithfulSMul Function IsAlgClosed IsAlgClosure IsPurelyInseparable PerfectRing in
  let p := ringChar F; rcases char_is_prime_or_zero F p with hp | hp
  · have := ExpChar.prime hp (R := F); have : Surjective (frobenius F p) := by
      intro b; let i := algebraMap F K; let n := exponent F K; have := isAlgClosed F (K := K)
      have ⟨x, hx⟩ := exists_pow_nat_eq (i b) (expChar_pow_pos F p (n + 1))
      use (elemReduct F x) ^ p ^ (n - elemExponent F x)
      apply (Injective.eq_iff (algebraMap_injective F K)).mp
      rw [←hx, frobenius_def, ←pow_mul, map_pow, algebraMap_elemReduct_eq' F p]
      ring_nf; rw [←pow_mul_pow_sub p (elemExponent_le_exponent F x)]; ring
    have := ofSurjective F p this; exact toPerfectField F p
  · have := (ringChar_zero_iff_CharZero F).mp hp; exact PerfectField.ofCharZero

/- If a field F admits a prime-degree extension which is algebraically closed, then that degree is 2;
   in addition, the field contains an element a such that -a is a square but a is not. -/
omit [FiniteDimensional F K] in
lemma finite_algebraic_closure_cyclic_quadratic {p : ℕ} [H : IsGalois F K] (hp : Nat.Prime p)
    (hrank : Module.finrank F K = p) : p = 2 ∧ ∃ a : F, ¬IsSquare a ∧ IsSquare (-a) := by
  open FiniteDimensional IsGalois Nat Polynomial in
  have hp1 := Prime.pos hp; have := fact_iff.mpr hp; have hK : (primitiveRoots p F).Nonempty := by
    have h_char := finite_algebraic_closure_cyclic_prime F K hp hrank
    have := natDegree_pos_iff_degree_pos.mpr (degree_cyclotomic_pos p F hp1)
    rcases divisor_by_finrank F K hrank hp this with ⟨z, hz⟩ | ⟨f, ⟨_, _⟩, _, hf3⟩
    · have : NeZero (p : F) := ⟨(CharP.charP_iff_prime_eq_zero hp).mpr.mt h_char⟩
      exact ⟨z, (mem_primitiveRoots hp1).mpr (isRoot_cyclotomic_iff.mp hz)⟩
    · have := natDegree_le_of_dvd hf3 (cyclotomic_ne_zero p F)
      rw [natDegree_cyclotomic p F, totient_prime hp] at this; grind
  have ⟨a, h2⟩ : ∃ a : F, Irreducible (X ^ p - C a) := by
    rw [←hrank] at hp1; have := of_finrank_pos hp1; have hG := card_aut_eq_finrank F K
    have h := fun hK ↦ (List.TFAE.out (isCyclic_tfae F K hK) 0 1).mp
    rw [hrank] at h hG; have ⟨a, _, _⟩ := h hK ⟨H, isCyclic_of_prime_card hG⟩; use a
  have hp2 : p = 2 := by
    by_contra; have h := fun n ↦ X_pow_sub_C_irreducible_iff_of_prime_pow hp this (K := F) (n := n)
    have h := (h 2 (by simp)).mpr ((h 1 (by simp)).mp (by rw [pow_one]; exact h2))
    have := Irreducible.natDegree_dvd_finrank h (pol_splits F K _)
    have := not_pos_pow_dvd (Prime.one_lt hp) one_lt_two; grind [natDegree_X_pow_sub_C]
  rw [hp2] at h2 hrank; let h := quadratic_algebraic_closure F K hrank 0 a; ring_nf at h
  have ha := nthRoots_two_eq_zero_iff.mp (roots_eq_zero_of_irreducible_of_natDegree_ne_one h2 ?_)
  refine ⟨hp2, ⟨a, ha, ?_⟩⟩; repeat aesop

/- A field containing a square root of -1 and admitting a finite extension which is algebraically
   closed is itself algebraically closed. -/
include K h in
lemma finite_algebraic_closure_with_i : IsAlgClosed F := open IntermediateField IsSquare Nat in
  have h_ac := IsAlgClosure.isAlgClosed F (K := K)
  have : PerfectField F := by
    let E := separableClosure F K; have : IsAlgClosure E K := ⟨h_ac, isAlgebraic_tower_top⟩
    have := finite_inseparable_algebraic_closure E K
    exact perfectField_of_isSeparable_of_perfectField_top F E
  have h : (⊥ : IntermediateField F K) = ⊤ := by
    apply bot_eq_top_iff_finrank_eq_one.mpr
    have := isGalois_iff.mpr ⟨inferInstance, IsAlgClosure.normal F K⟩
    rw [←IsGaloisGroup.card_eq_finrank Gal(K/F), card_eq_fintype_card]
    by_contra; have ⟨p, hp1, hp1a⟩ := exists_prime_and_dvd this; have := fact_iff.mpr hp1
    obtain ⟨g, rfl⟩ := exists_prime_orderOf_dvd_card p hp1a; let H := Subgroup.zpowers g
    let E := fixedField H; have : IsAlgClosure E K := ⟨h_ac, isAlgebraic_tower_top⟩
    have h_ekrank := finrank_fixedField_eq_card H; rw [card_zpowers] at h_ekrank
    have ⟨_, ⟨_, _, hs⟩⟩ := finite_algebraic_closure_cyclic_quadratic E K hp1 h_ekrank
    have h := mul (map (algebraMap F ↥E) h) hs; simp at h; contradiction
  IsAlgClosed.of_ringEquiv K F (topEquiv.symm.trans ((equivOfEq h).symm.trans (botEquiv F K)))
