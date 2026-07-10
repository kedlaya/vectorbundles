module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import VectorBundles.ArtinSchreier.ArtinSchreierExt

@[expose] public section

open IntermediateField Module Nat Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [Hac: IsAlgClosed K]

/- The degree of any irreducible polynomial divides the degree of the algebraic closure .-/
lemma finrank_divides {f : F[X]} (h : Irreducible f) : f.natDegree ∣ finrank F K :=
  Irreducible.natDegree_dvd_finrank h (IsAlgClosed.splits (f.map _))

/- If a field admits an algebraically closed extension of degree dividing a prime p, any polynomial
   over this field either has a root or:
     - only has irreducible divisors of degree p;
     - has degree divisible by p.  -/
lemma divisor_by_finrank (f : F[X]) (hr : finrank F K ∣ p) (hp : p.Prime) :
    (∃ x, f.IsRoot x) ∨ (∀ d, Irreducible d → d ∣ f → d.natDegree = p) := by
  rw [or_iff_not_imp_right]; push Not; rintro ⟨d, h1, h2, h3⟩
  have h := ((dvd_prime hp).mp ((finrank_divides F K h1).trans hr)).resolve_right h3
  have ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h; exact ⟨x, IsRoot.dvd hx h2⟩

lemma divisor_by_finrank' (f : F[X]) (hr : finrank F K ∣ p) (hp : p.Prime) :
    (∃ x, f.IsRoot x) ∨ p ∣ f.natDegree := by open Multiset PrincipalIdealRing in
  refine Or.imp_right ?_ (divisor_by_finrank F K f hr hp); by_cases h0 : f = 0; · simp_all
  have ⟨hi, hS⟩ := factors_spec _ h0; have h2 := prod_eq_zero.mt (hS.symm.ne_zero_iff.mp h0)
  intro h1; rw [←natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hS)]
  rw [natDegree_multiset_prod _ h2]; apply dvd_sum; simp only [mem_map]
  rintro - ⟨d, he, rfl⟩; exact (h1 d (hi d he) (hS.dvd_iff_dvd_right.mp (dvd_prod he))).symm.dvd

/- If a field admits a Galois extension of prime degree p which is algebraically closed, then
   its characteristic cannot equal p. -/
lemma finite_alg_closure_prime [IsGalois F K] (hp : p.Prime) (hr : finrank F K = p) : ¬CharP F p
  := by let t := p-1; subst hr; have := FiniteDimensional.of_finrank_pos hp.pos; open Field in
  by_contra; have h_a {E} [Field E] (x : E) := (artinSchreierPoly_isMonicOfDegree x hp.one_lt).1
  have ⟨a, x, ha⟩ := cyclic_char_p_as_param F K hp rfl; have := artin_schreier_tower F K hp a x ha
  have h := coe_lt_degree.mpr ((h_a ((algebraMap F K) a * x^t)).trans_gt hp.pos); have h_d := h_a a
  rw [←ha] at h_d; have ⟨y, hy⟩ := Hac.exists_aeval_eq_zero K _ h.ne'
  simp_all [t, (primitive_element_iff_minpoly_natDegree_eq F x).mpr h_d]

/- A field admitting a finite purely inseparable extension which is algebraically closed
   is perfect (and hence itself algebraically closed). -/
lemma finite_insep_alg_closure [FiniteDimensional F K] [IsPurelyInseparable F K] : PerfectField F
  := by open CharP FaithfulSMul Function IsPurelyInseparable in
  let p := ringChar F; let n := exponent F K; rcases char_is_prime_or_zero F p with h | h
  · have := ExpChar.prime h (R := F); have h : Surjective (frobenius F p) := by
      intro b; have h := Hac.exists_pow_nat_eq ((algebraMap F K) b) (expChar_pow_pos F p (n + 1))
      obtain ⟨x, hx⟩ := h; rw [pow_succ', ←pow_mul_pow_sub p (elemExponent_le_exponent F x)] at hx
      use elemReduct F x ^ p ^ (n - elemExponent F x); apply (algebraMap_injective F K).eq_iff.mp
      rw [←hx, frobenius_def, ←pow_mul, map_pow, algebraMap_elemReduct_eq' F p]; ring
    open PerfectRing in have := ofSurjective F p h; exact toPerfectField F p
  · have := (ringChar_zero_iff_CharZero F).mp h; exact PerfectField.ofCharZero

/- If a and b belong to a field which admits an algebraically closed quadratic extension,
   then one of a^2+b or -b is a square. -/
lemma quadratic_alg_closure (h : finrank F K ∣ 2) (a b : F) : IsSquare (a*a+b) ∨ IsSquare (-b) :=
  let g := monomial 4 1 + monomial 2 (-2*a) + monomial 0 (a^2 + b); by open Finset in
  have h1 : g.IsMonicOfDegree 4 := by subst g; exact ⟨by compute_degree!, by monicity⟩
  rcases divisor_by_finrank F K g h prime_two with ⟨x, hx⟩ | h
  · right; use x^2 - a; simp only [IsRoot.def, g, eval_add, eval_monomial] at hx; grind only
  · have h := exists_monic_irreducible_factor g (not_isUnit_of_natDegree_pos g (by simp [h1.1]))
    obtain ⟨f, h3, h4, ⟨e, he⟩⟩ := h; have hf : f.IsMonicOfDegree 2 := ⟨h f h4 ⟨e, he⟩, h3⟩
    subst g; let f₀ := f.coeff 0; let f₁ := f.coeff 1; let e₀ := e.coeff 0; let e₁ := e.coeff 1
    have : f₀*e₀ = a^2 + b ∧ f₀*e₁ + f₁*e₀ = 0 ∧ f₀ + f₁*e₁ + e₀ = -2*a ∧ f₁ + e₁ = 0 := by
      have h : ∀ {t : F[X]}, t.IsMonicOfDegree 2 → t.coeff 2 = 1 ∧ t.coeff 3 = 0 := by
        intro _ h; rw [←h.1]; simp [h.2, natDegree_le_iff_coeff_eq_zero.mp h.1.le]
      have hm := fun n ↦ (coeff_mul f e n).symm; simp only [←he, coeff_add, coeff_monomial] at hm
      open And in have hm' := intro (hm 0) (intro (hm 1) (intro (hm 2) (hm 3))); rw [he] at h1
      simp [antidiagonal, h hf, h (hf.of_mul_left h1)] at hm'; ring_nf at hm' ⊢; exact hm'
    clear h1 h he; by_cases f₁ = 0; right; use f₀ + a; grind only; · left; use f₀; grind only

/- A field containing a square root of -1 and admitting a finite extension which is algebraically
   closed is itself algebraically closed. -/
lemma finite_alg_closure_i [FiniteDimensional F K] (hm : IsSquare (-1 : F)) : IsAlgClosed F := by
  let E := separableClosure F K; have := finite_insep_alg_closure E K
  have := perfectField_of_isSeparable_of_perfectField_top F E
  have : IsAlgClosure F K := ⟨Hac, inferInstance⟩; have h : finrank F K = 1 := by open IsGalois in
    by_contra h; have ⟨p, hp, hd⟩ := exists_prime_and_dvd h; have := fact_iff.mpr hp
    rw [←card_aut_eq_finrank] at hd; have ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
    let H := Subgroup.zpowers g; have hr := finrank_fixedField_eq_card H; let E := fixedField H
    rw [card_zpowers, hg] at hr; have h_char := finite_alg_closure_prime E K hp hr
    have hG := card_aut_eq_finrank E K; have hK : (primitiveRoots p E).Nonempty := by
      rcases divisor_by_finrank' E K _ hr.dvd hp with ⟨z, hz⟩ | hz
      · have := neZero_iff.mpr ((CharP.charP_iff_prime_eq_zero hp).mpr.mt h_char)
        exact ⟨z, (mem_primitiveRoots hp.pos).mpr (isRoot_cyclotomic_iff.mp hz)⟩
      · simp [hp.one_lt.not_ge, natDegree_cyclotomic p E, totient_prime hp] at hz
    have h := fun hK ↦ (List.TFAE.out (isCyclic_tfae E K hK) 0 1).mp; rw [hr] at h hG
    have ⟨a, h2, _⟩ := h hK ⟨inferInstance, isCyclic_of_prime_card hG⟩; have hp : p = 2 := by
      by_contra h1; have h := fun n ↦ X_pow_sub_C_irreducible_iff_of_prime_pow hp h1 (K := E)
        (n := n); have h := (h 2 (by simp)).mpr ((h 1 (by simp)).mp (by rw [pow_one]; exact h2))
      have h := finrank_divides _ K h; rw [hr] at h; simp_all [not_pos_pow_dvd hp.one_lt]
    rw [hp] at h2 hr; let h := quadratic_alg_closure _ K hr.dvd 0 a; ring_nf at h
    have ha := nthRoots_two_eq_zero_iff.mp (roots_eq_zero_of_irreducible_of_natDegree_ne_one h2 ?_)
    have := (hm.map (algebraMap F _)).mul (h.resolve_left ha); repeat aesop
  have h := equivOfEq (bot_eq_top_iff_finrank_eq_one.mpr h)
  exact IsAlgClosed.of_ringEquiv K F (((botEquiv F K).symm.trans h).trans topEquiv).symm

/- A field in which -1 is not a square, but adjoining its square root gives an algebraic
   closure, is real closed. -/
omit Hac in lemma RealClosed_from_quadratic (h1 : ¬IsSquare (-1 : F))
    (h2 : ∃ i : K, i^2 = -1 ∧ IsAlgClosed F⟮i⟯) : IsRealClosed F := by open IsIntegral minpoly in
  obtain ⟨i, h2a, _⟩ := h2; have hd := X_pow_add_C_ne_zero two_pos (1 : F); open adjoin in
  have h := natDegree_le_of_dvd (dvd_iff (x := i).mpr ?_) hd; rw [natDegree_X_pow_add_C] at h
  have hi : IsIntegral F i := by apply of_pow two_pos; rw [h2a]; exact isIntegral_one.neg
  have hr : finrank F F⟮i⟯ ∣ 2 := (dvd_prime prime_two).mpr (by grind [finrank hi, natDegree_pos])
  have hq := quadratic_alg_closure F F⟮i⟯ hr; have hssq : ∀ x : F, IsSumSq x → IsSquare x := by
    apply IsSumSq.rec'; simp; rintro a b ⟨y, rfl⟩ - h; by_cases h0 : b = 0; · simp_all
    contrapose h1; rw [←neg_div_self h0]; exact ((hq y b).resolve_left h1).div h
  have := isSemireal_iff_not_isSumSq_neg_one.mpr ((hssq _).mt h1)
  let issquare := hq 0; ring_nf at issquare; refine ⟨issquare, ?_⟩; intro f _
  rcases divisor_by_finrank' F F⟮i⟯ f hr prime_two with h | _; exact h; grind; · aesop

/- The Artin-Schreier theorem: a field admitting a finite extension which is algebraically closed
   is either algebraically closed or real closed. -/
theorem artin_schreier_thm [FiniteDimensional F K] : IsAlgClosed F ∨ IsRealClosed F := by
  by_cases hF : IsSquare (-1 : F); left; exact finite_alg_closure_i F K hF; /- -/ right
  have ⟨i, hi⟩ := Hac.exists_pow_nat_eq (-1) two_pos; have h := finite_alg_closure_i F⟮i⟯ K ?_
  exact RealClosed_from_quadratic F K hF ⟨i, ⟨hi, h⟩⟩
  apply (isSquare_iff_exists_sq _).mpr; symm at hi; aesop
