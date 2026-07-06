module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import VectorBundles.ArtinSchreier.ArtinSchreierExt

@[expose] public section

open IntermediateField Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [Hac: IsAlgClosed K]

/- The degree of any irreducible polynomial divides the degree of the algebraic closure .-/
lemma finrank_divides {f : F[X]} (h : Irreducible f) : f.natDegree ∣ finrank F K :=
  Irreducible.natDegree_dvd_finrank h (IsAlgClosed.splits (map (algebraMap F K) f))

/- If a field admits an algebraically closed extension of degree dividing a prime p, any polynomial
   over this field either has a root or:
     - only has irreducible divisors of degree p;
     - has degree divisible by p.  -/
lemma divisor_by_finrank (f : F[X]) {p : ℕ} (hr : finrank F K ∣ p) (hp : Nat.Prime p) :
  (∃ x, f.IsRoot x) ∨ (∀ d, Irreducible d → d ∣ f → d.natDegree = p) := by open Nat in
  by_cases h : ∃ x, f.IsRoot x; left; exact h; right; intro d hd1 hd2
  rcases Prime.eq_one_or_self_of_dvd hp _ ((finrank_divides F K hd1).trans hr) with h | h
  have ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h; grind [IsRoot.dvd hx hd2]; /- -/ exact h

lemma divisor_by_finrank' (f : F[X]) {p : ℕ} (hr : finrank F K ∣ p) (hp : Nat.Prime p):
  (∃ x, f.IsRoot x) ∨ p ∣ f.natDegree := by open Multiset UniqueFactorizationMonoid in
  rcases divisor_by_finrank F K f hr hp with h | h1; left; exact h; right; let S := factors f
  by_cases h0 : f = 0; simp_all; /- -/ push Not at h0; have hS := (factors_prod h0).symm
  have h2 : S.prod ≠ 0 := by grind only [(associated_zero_iff_eq_zero f).mp.mt h0]
  have hd := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hS)
  rw [hd, natDegree_multiset_prod S (prod_eq_zero.mt h2)]; apply dvd_sum; simp
  intro d hd; exact (h1 d (irreducible_of_factor d hd) (dvd_of_mem_factors hd)).symm.dvd

/- If a field admits a Galois extension of prime degree p which is algebraically closed, then
   its characteristic cannot equal p. -/
lemma finite_algebraic_closure_cyclic_prime {p : ℕ} [IsGalois F K] (hp : Nat.Prime p)
    (hr : finrank F K = p) : ¬CharP F p := by
  by_contra; open CanLift FiniteDimensional IsAlgClosed minpoly Subfield in
  have hp0 := Nat.Prime.pos hp; have hp1 := Nat.Prime.one_lt hp
  have h_a {E : Type} [Field E] (x : E) := (artinSchreierPoly_isMonicOfDegree x hp1).1
  have ⟨a, x, ha⟩ := cyclic_char_p_as_param F K hp hr; have h_d := h_a a; rw [←ha] at h_d
  have h := degree_ne_of_natDegree_ne ((h_a ((algebraMap F K) a * x^(p-1))).trans_gt hp0).ne'
  have ⟨y, hy⟩ := exists_aeval_eq_zero K _ h; simp [sub_sub, sub_eq_zero] at hy; subst hr
  have := of_finrank_pos hp0; obtain ⟨y₀, rfl⟩ : ∃ y₀ : F⟮x⟯, y₀ = y := by
    rw [(Field.primitive_element_iff_minpoly_natDegree_eq F x).mpr h_d]; exact prf y (mem_top y)
  have := artin_schreier_tower F K hp a x ha; grind only

/- A field admitting a finite purely inseparable extension which is algebraically closed
   is perfect (and hence itself algebraically closed). -/
lemma finite_inseparable_algebraic_closure [FiniteDimensional F K] [IsPurelyInseparable F K] :
    PerfectField F := by open CharP FaithfulSMul Function IsPurelyInseparable PerfectRing in
  let p := ringChar F; rcases char_is_prime_or_zero F p with hp | hp
  · have := ExpChar.prime hp (R := F); have : Surjective (frobenius F p) := by
      intro b; let i := algebraMap F K; let n := exponent F K
      have ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (i b) (expChar_pow_pos F p (n + 1))
      use (elemReduct F x) ^ p ^ (n - elemExponent F x)
      apply (Injective.eq_iff (algebraMap_injective F K)).mp
      rw [←hx, frobenius_def, ←pow_mul, map_pow, algebraMap_elemReduct_eq' F p]
      ring_nf; rw [←pow_mul_pow_sub p (elemExponent_le_exponent F x)]; ring
    have := ofSurjective F p this; exact toPerfectField F p
  · have := (ringChar_zero_iff_CharZero F).mp hp; exact PerfectField.ofCharZero

/- If a and b belong to a field which admits an algebraically closed quadratic extension,
   then one of a^2+b or -b is a square. -/
lemma quadratic_alg_closure (h : finrank F K ∣ 2) (a b : F) :
    IsSquare (a*a+b) ∨ IsSquare (-b) := by open And Finset IsMonicOfDegree in
  let g := monomial 4 1 + monomial 2 (-2 * a) + monomial 0 (a^2 + b); let h2 := Nat.prime_two
  have h1 : g.IsMonicOfDegree 4 := by subst g; exact ⟨by compute_degree!, by monicity⟩
  rcases divisor_by_finrank F K g h h2 with ⟨x, hx⟩ | h
  · right; use x^2 - a; simp only [IsRoot.def, g, eval_add, eval_monomial] at hx; grind only
  · have ⟨f, hf2, h4, ⟨e, he⟩⟩ := exists_monic_irreducible_factor g (not_isUnit_of_natDegree_pos
      g (by grind [h1.1])); have hf : f.IsMonicOfDegree 2 := ⟨h f h4 ⟨e, he⟩, hf2⟩; subst g
    let f₀ := f.coeff 0; let f₁ := f.coeff 1; let e₀ := e.coeff 0; let e₁ := e.coeff 1
    have : f₀*e₀ = a^2 + b ∧ f₀*e₁ + f₁*e₀ = 0 ∧ f₀ + f₁*e₁ + e₀ = -2*a ∧ f₁ + e₁ = 0 := by
      have h : ∀ {t : F[X]}, t.IsMonicOfDegree 2 → t.coeff 2 = 1 ∧ t.coeff 3 = 0 := by
        intro t h; rw [←h.1]; simp [h.2, natDegree_le_iff_coeff_eq_zero.mp h.1.le 3]
      have hm := fun n ↦ (coeff_mul f e n).symm; rw [←he] at hm
      have hm' := intro (hm 0) (intro (hm 1) (intro (hm 2) (hm 3)))
      simp only [coeff_add, coeff_monomial, antidiagonal] at hm'
      rw [he] at h1; simp [h hf, h (of_mul_left hf h1)] at hm'; ring_nf at hm' ⊢; exact hm'
    clear h1 h he; by_cases f₁ = 0; right; use f₀ + a; grind only; left; use f₀; grind only

/- If a field F admits a prime-degree Galois extension which is algebraically closed, then
   -1 is not a square in F. -/
lemma finite_algebraic_closure_cyclic_quadratic {p : ℕ} [H : IsGalois F K] (hp : Nat.Prime p)
    (hr : Module.finrank F K = p) : ¬IsSquare (-1 : F) := by
  open FiniteDimensional IsGalois IsSquare Nat Or Polynomial in
  have hp0 := Prime.pos hp; have := fact_iff.mpr hp; have hK : (primitiveRoots p F).Nonempty := by
    have h_char := finite_algebraic_closure_cyclic_prime F K hp hr; have hp1 := Prime.one_lt hp
    rcases divisor_by_finrank' F K _ hr.dvd hp with ⟨z, hz⟩ | hz
    · have : NeZero (p : F) := ⟨(CharP.charP_iff_prime_eq_zero hp).mpr.mt h_char⟩
      exact ⟨z, (mem_primitiveRoots hp0).mpr (isRoot_cyclotomic_iff.mp hz)⟩
    · rw [natDegree_cyclotomic p F, totient_prime hp] at hz
      have := le_of_dvd (zero_lt_sub_of_lt hp1) hz; grind only
  rw [←hr] at hp0; have := of_finrank_pos hp0; have hG := card_aut_eq_finrank F K
  have h := fun hK ↦ (List.TFAE.out (isCyclic_tfae F K hK) 0 1).mp; rw [hr] at h hG
  have ⟨a, h2, _⟩ := h hK ⟨H, isCyclic_of_prime_card hG⟩
  have hp : p = 2 := by
    by_contra; have h := fun n ↦ X_pow_sub_C_irreducible_iff_of_prime_pow hp this (K := F) (n := n)
    have h := (h 2 (by simp)).mpr ((h 1 (by simp)).mp (by rw [pow_one]; exact h2))
    have := finrank_divides F K h; have := not_pos_pow_dvd (Prime.one_lt hp) one_lt_two; simp_all
  rw [hp] at h2 hr; let h := quadratic_alg_closure F K hr.dvd 0 a; ring_nf at h; by_contra
  have ha := nthRoots_two_eq_zero_iff.mp (roots_eq_zero_of_irreducible_of_natDegree_ne_one h2 ?_)
  have h := mul this (resolve_left h ha); repeat aesop

/- A field containing a square root of -1 and admitting a finite extension which is algebraically
   closed is itself algebraically closed. -/
lemma finite_algebraic_closure_with_i [FiniteDimensional F K] (h : IsSquare (-1 : F)) :
    IsAlgClosed F := open IntermediateField IsSquare Nat in
  let E := separableClosure F K; have := finite_inseparable_algebraic_closure E K
  have : PerfectField F := perfectField_of_isSeparable_of_perfectField_top F E
  have h : (⊥ : IntermediateField F K) = ⊤ := by
    apply bot_eq_top_iff_finrank_eq_one.mpr; have : IsAlgClosure F K := ⟨Hac, inferInstance⟩
    have := isGalois_iff.mpr ⟨inferInstance, IsAlgClosure.normal F K⟩
    rw [←IsGaloisGroup.card_eq_finrank Gal(K/F), card_eq_fintype_card]
    by_contra; have ⟨p, hp1, hp2⟩ := exists_prime_and_dvd this; have := fact_iff.mpr hp1
    obtain ⟨g, rfl⟩ := exists_prime_orderOf_dvd_card p hp2; let H := Subgroup.zpowers g
    let E := fixedField H; have hr := finrank_fixedField_eq_card H; rw [card_zpowers] at hr
    have := finite_algebraic_closure_cyclic_quadratic E K hp1 hr
    have h := map (algebraMap F ↥E) h; simp at h; contradiction
  IsAlgClosed.of_ringEquiv K F (topEquiv.symm.trans ((equivOfEq h).symm.trans (botEquiv F K)))

/- A field in which -1 is not a square, but adjoining a square root of -1 gives an algebraic
   closure, is real closed. -/
omit Hac in lemma RealClosed_from_quadratic (h1 : ¬IsSquare (-1 : F))
    (h2 : ∃ i : K, i^2 = -1 ∧ IsAlgClosed F⟮i⟯) : IsRealClosed F := by
  open IsIntegral Multiset Nat UniqueFactorizationMonoid in /- -/
  obtain ⟨i, h2a, _⟩ := h2; have hr : finrank F F⟮i⟯ ∣ 2 := by open minpoly in
    have h_int : IsIntegral F i := by apply of_pow two_pos; rw [h2a]; exact neg isIntegral_one
    rw [adjoin.finrank h_int]; have h := X_pow_add_C_ne_zero two_pos (1 : F)
    have h := natDegree_le_of_dvd (dvd_iff (x := i).mpr (by aesop)) h; have := natDegree_pos h_int
    rw [natDegree_X_pow_add_C] at h; let t := (minpoly F i).natDegree
    have h : t = 1 ∨ t = 2 := ?_; subst t; rcases h with h | h; repeat (rw [h]; grind)
  have ng : ∀ x : F, 0 ≠ x → IsSquare x → ¬IsSquare (-x) := by
    intro _ _ hs; by_contra; grind only [IsSquare.div this hs]
  have hq := quadratic_alg_closure F F⟮i⟯ hr; have hssq : ∀ x : F, IsSumSq x → IsSquare x := by
    apply IsSumSq.rec'; exact IsSquare.zero; rintro a b ⟨y, rfl⟩ _ hb; by_cases hb0 : 0 = b
    rw [←hb0, add_zero]; use y; /- -/ exact Or.resolve_right (hq y b) (ng b hb0 hb)
  have := isSemireal_iff_not_isSumSq_neg_one.mpr ((hssq (-1)).mt (ng 1 zero_ne_one IsSquare.one))
  let issquare := hq 0; ring_nf at issquare; refine ⟨issquare, ?_⟩; intro f _
  rcases divisor_by_finrank' F F⟮i⟯ f hr prime_two with h | h1; exact h; grind only [=odd_iff]

/- A field admitting an algebraic closure which is a finite extension is either algebraically
   closed or real closed. -/
theorem artin_schreier_thm [FiniteDimensional F K] : IsAlgClosed F ∨ IsRealClosed F := by
  open Algebra.IsIntegral IsAlgClosed IsIntegral Nat SetLike in
  by_cases hF : IsSquare (-1 : F)
  · left; exact finite_algebraic_closure_with_i F K hF
  · right; have ⟨i, hi⟩ := exists_pow_nat_eq (-1 : K) two_pos; symm at hi
    have := finite_algebraic_closure_with_i F⟮i⟯ K ((isSquare_iff_exists_sq (-1)).mpr (by aesop))
    exact RealClosed_from_quadratic F K hF ⟨i, ⟨hi.symm, this⟩⟩
