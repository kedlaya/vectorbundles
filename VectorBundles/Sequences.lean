
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Defs

@[expose] public section

lemma sequence_argument1 (n : ℕ) (m : ℕ → ℤ)
  (h1 : ∀ i : ℕ, i + 1 < n → m (i + 1) ≤ m i + 1)
  (h2 : ¬ ∃ (i j : ℕ), j < n → m j = m i + 2 ∧ ∀ (k : ℕ), k < i → i < j )
  : ∀ (i j : ℕ), i < j → j < n → m j ≤ m i + 1 :=  by
  have h : ∀ d : ℕ, ∀ (i j : ℕ), j - i ≤ d + 1 → i < j → j < n → m j ≤ m i + 1 := by
    intro d
    induction d with
      | zero =>
        intro i j h3 h4 h5
        grind
      | succ d hyp =>
        intro i j
        by_cases j - i ≤ d + 1
        · intro h1 h2 h3
          grind
        · intro h4
          have _ : j - i = d + 2 := by grind
          by_contra
          push Not at this
          obtain ⟨h2, h3, h4⟩ := this
          let mid := m i + 1
          have h_mid : ∀ k : ℕ, i < k → k < j → m k = mid ∧ m j = mid + 1 := by
            intro k h5 h6
            let hyp1 := hyp
            have h1' : k - i ≤ d + 1 := by grind
            have h2' : i < k := by grind
            have h3' : k < n := by grind
            specialize hyp1 i k h1' h2' h3'
            let hyp2 := hyp
            have h1'' : j - k ≤ d + 1 := by grind
            have h2'' : k < j := by grind
            specialize hyp2 k j h1'' h2'' h3
            grind
          have h_j : m j = mid + 1 := by
            have h_j1 : i < i + 1 := by grind
            have h_j2 : i + 1 < j := by grind
            specialize h_mid (i + 1) h_j1 h_j2
            obtain ⟨_, h_j3⟩ := h_mid
            apply h_j3
          have h_k : ∀ k : ℕ, i < k → k < j → m k = mid ∧ m j = mid + 1 := by
            grind
          grind
  intro i j h1 h2
  specialize h (j - i) i j
  grind

lemma sequence_argument2 (n : ℕ) (m : ℕ → ℤ)
  (h1: ∑ a ∈ Finset.range n, m a = 0)
  (h2: ∀ i : ℕ, i < n → ∑ a ∈ Finset.range i, m a ≤ 0)
  (h3: ∀ (i j : ℕ), i < j → j < n → m j ≤ m i + 1 ) :
  ∀ i : ℕ, i < n → m i = 0 := by
  induction n with
  | zero => grind
  | succ n hyp =>
    by_cases n = 0
    · have _ : (∑ a ∈ Finset.range 1, m a) = m 0 := by
        exact Finset.sum_range_one m
      simp_all
    · have h_split : (∑ a ∈ Finset.range n, m a) + m n = ∑ a ∈ Finset.range (n+1), m a := by
        exact Eq.symm (Finset.sum_range_succ m n)
      have _ : m n ≥ 0 := by
        have _ : n < n + 1 := by
          exact Nat.lt_succ_self n
        specialize h2 n
        simp_all
        grind
      have h4 : ∃ i : ℕ, i < n ∧ m i ≤ 0 := by
        have _ : n < n + 1 := by
          exact Nat.lt_succ_self n
        specialize h2 n
        have _ : ∑ a ∈ Finset.range n, m a ≤ 0 := by
          apply h2
          simp
        by_contra
        push Not at this
        have _ : ∀ i < n, 1 ≤ m i := by
          intro i
          apply this
        have _ : ∑ a ∈ Finset.range n, (m a - 1) ≥ 0 := by
          apply Finset.sum_nonneg
          grind
        have _ : ∑ a ∈ Finset.range n, (m a - 1) = (∑ a ∈ Finset.range n, m a) - (∑ a ∈ Finset.range n, 1) := by
          exact Finset.sum_sub_distrib m fun x => 1
        have _ : ∑ a ∈ Finset.range n, 1 = n := by
          exact Finset.sum_range_induction (fun k => 1) (fun n => n) rfl n fun k => congrFun rfl
        have _ : ∑ a ∈ Finset.range n, m a ≥ n := by
          simp_all
        grind
      obtain ⟨i, h4a, h4b⟩ := h4
      have _ : m n ≤ 1 := by
        specialize h3 i n
        simp_all
        grind
      have _ : m n ≠ 1 := by
        by_contra
        have _ : ∀ j : ℕ, j < n → m j ≥ 0 := by
          intro j hj
          specialize h3 j n
          simp_all
        have _ : ∑ a ∈ Finset.range n, m a ≥ 0 := by
          apply Finset.sum_nonneg
          grind
        grind
      have _ : m n = 0 := by
        grind
      have h1' : ∑ a ∈ Finset.range n, m a = 0 := by
        grind
      grind
