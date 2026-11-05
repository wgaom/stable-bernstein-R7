import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace R7.Core.Gram
open scoped BigOperators

noncomputable def chain (d b x : ℕ → ℝ) : ℕ → ℝ
  | 0 => d 0 * x 0 ^ 2
  | n+1 => chain d b x n + 2*b n*x n*x (n+1) + d (n+1)*x (n+1)^2

theorem chain_squares (d b p x : ℕ → ℝ) (n : ℕ)
    (hp : ∀ j ≤ n, p j ≠ 0) (hzero : d 0 = p 0)
    (hstep : ∀ j < n, d (j+1) = p (j+1) + b j^2 / p j) :
    chain d b x n =
      (∑ j ∈ Finset.range n, p j*(x j+b j/p j*x (j+1))^2) + p n*x n^2 := by
  induction n with
  | zero => simp [chain, hzero]
  | succ n ih =>
    rw [chain, ih (fun j hj => hp j (by omega))
      (fun j hj => hstep j (by omega)), Finset.sum_range_succ, hstep n (by omega)]
    have hn := hp n (by omega)
    field_simp
    ring

theorem chain_pos (d b p x : ℕ → ℝ) (n : ℕ)
    (hp : ∀ j ≤ n, 0 < p j) (hzero : d 0 = p 0)
    (hstep : ∀ j < n, d (j+1) = p (j+1) + b j^2 / p j)
    (hx : ∃ j ≤ n, x j ≠ 0) : 0 < chain d b x n := by
  induction n with
  | zero =>
    have hxx : x 0 ≠ 0 := by
      rcases hx with ⟨j,hj,hx⟩
      have hj0 : j=0 := by omega
      simpa [hj0] using hx
    simpa [chain, hzero] using mul_pos (hp 0 (by omega)) (sq_pos_of_ne_zero hxx)
  | succ n ih =>
    by_cases hn : x (n+1) = 0
    · have hprev : ∃ j ≤ n, x j ≠ 0 := by
        rcases hx with ⟨j,hj,hx⟩
        refine ⟨j, ?_, hx⟩
        by_contra hh
        have : j=n+1 := by omega
        exact hx (by simpa [this] using hn)
      have he := ih (fun j hj => hp j (by omega))
        (fun j hj => hstep j (by omega)) hprev
      simpa [chain, hn] using he
    · rw [chain_squares d b p x (n+1) (fun j hj => ne_of_gt (hp j hj)) hzero hstep]
      have hsum : 0 ≤ ∑ j ∈ Finset.range (n+1), p j*(x j+b j/p j*x (j+1))^2 :=
        Finset.sum_nonneg fun j hj => mul_nonneg (le_of_lt (hp j (by have := Finset.mem_range.mp hj; omega))) (sq_nonneg _)
      exact add_pos_of_nonneg_of_pos hsum (mul_pos (hp (n+1) (by omega)) (sq_pos_of_ne_zero hn))

noncomputable def delta (d b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => d 0
  | n+2 => d (n+1)*delta d b (n+1)-b n^2*delta d b n

theorem continuants_pos (d b x : ℕ → ℝ) (n : ℕ)
    (hd : ∀ j ≤ n+1, 0 < delta d b j)
    (hx : ∃ j ≤ n, x j ≠ 0) : 0 < chain d b x n := by
  let p := fun j => delta d b (j+1)/delta d b j
  apply chain_pos d b p x n
  · intro j hj
    exact div_pos (hd (j+1) (by omega)) (hd j (by omega))
  · simp [p,delta]
  · intro j hj
    dsimp [p]
    rw [delta]
    have h1 := ne_of_gt (hd (j+1) (by omega))
    have h0 := ne_of_gt (hd j (by omega))
    field_simp
    ring
  · exact hx

theorem tridiagonal_polynomial_pos (a : ℕ → ℝ) (n : ℕ)
    (hd : ∀ j ≤ n+1, 0 < delta (fun j => 2*a (2*j)) (fun j => a (2*j+1)) j)
    (u : ℝ) :
    0 < chain (fun j => 2*a (2*j)) (fun j => a (2*j+1)) (fun j => u^j) n / 2 := by
  have h := continuants_pos (fun j => 2*a (2*j)) (fun j => a (2*j+1))
    (fun j => u^j) n hd ⟨0, Nat.zero_le _, by simp⟩
  positivity

theorem monomial_chain (a : ℕ → ℝ) (u : ℝ) (n : ℕ) :
    chain (fun j => 2*a (2*j)) (fun j => a (2*j+1)) (fun j => u^j) n =
      2*∑ k ∈ Finset.range (2*n+1), a k*u^k := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    rw [chain, ih]
    have hn : 2*(n+1)+1 = (2*n+1)+1+1 := by omega
    have hs : (∑ k ∈ Finset.range (2*(n+1)+1), a k*u^k) =
        (∑ k ∈ Finset.range (2*n+1), a k*u^k)+a (2*n+1)*u^(2*n+1)+a (2*n+2)*u^(2*n+2) := by
      rw [hn, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [hs]
    have hu : u^n*u^(n+1) = u^(2*n+1) := by rw [← pow_add]; congr 1; omega
    have hv : (u^(n+1))^2 = u^(2*n+2) := by rw [← pow_mul]; congr 1; omega
    have he : 2*a (2*n+1)*u^n*u^(n+1) = 2*a (2*n+1)*u^(2*n+1) := by
      calc
        _ = 2*a (2*n+1)*(u^n*u^(n+1)) := by ring
        _ = _ := by rw [hu]
    rw [hv, he]
    have hn2 : 2*(n+1) = 2*n+2 := by omega
    rw [hn2]
    ring

theorem power_polynomial_pos (a : ℕ → ℝ) (n : ℕ)
    (hd : ∀ j ≤ n+1, 0 < delta (fun j => 2*a (2*j)) (fun j => a (2*j+1)) j)
    (u : ℝ) : 0 < ∑ k ∈ Finset.range (2*n+1), a k*u^k := by
  have h := tridiagonal_polynomial_pos a n hd u
  rw [monomial_chain] at h
  linarith

noncomputable def bandDelta (d b : ℕ → ℝ) (z : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => d 0
  | 2 => d 0*d 1-b 0^2
  | 3 => d 0*d 1*d 2+2*b 0*b 1*z-d 0*b 1^2-d 1*z^2-d 2*b 0^2
  | n+4 => d (n+3)*bandDelta d b z (n+3)-b (n+2)^2*bandDelta d b z (n+2)

noncomputable def reducedDiagonal (d b : ℕ → ℝ) (z : ℝ) : ℕ → ℝ
  | 0 => d 1-b 0^2/d 0
  | 1 => d 2-z^2/d 0
  | n+2 => d (n+3)

noncomputable def reducedOff (d b : ℕ → ℝ) (z : ℝ) : ℕ → ℝ
  | 0 => b 1-b 0*z/d 0
  | n+1 => b (n+2)

theorem bandDelta_reduced (d b : ℕ → ℝ) (z : ℝ) (hd : d 0 ≠ 0) (n : ℕ) :
    delta (reducedDiagonal d b z) (reducedOff d b z) n = bandDelta d b z (n+1)/d 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simp [delta,bandDelta,hd]
    rcases n with _ | n
    · simp only [delta,reducedDiagonal,bandDelta]
      field_simp

    rcases n with _ | n
    · simp only [delta,reducedDiagonal,reducedOff,bandDelta]
      field_simp
      ring
    · rw [delta]
      rw [ih (n+2) (by omega), ih (n+1) (by omega)]
      simp only [reducedDiagonal,reducedOff,bandDelta]
      ring

theorem band_schur_identity (d b x : ℕ → ℝ) (z : ℝ) (hd : d 0 ≠ 0) (n : ℕ) :
    chain d b x (n+2)+2*z*x 0*x 2 =
      d 0*(x 0+b 0/d 0*x 1+z/d 0*x 2)^2+
        chain (reducedDiagonal d b z) (reducedOff d b z) (fun j => x (j+1)) (n+1) := by
  induction n with
  | zero =>
    simp only [chain,reducedDiagonal,reducedOff]
    field_simp
    ring
  | succ n ih =>
    have he : chain d b x (n+1+2)+2*z*x 0*x 2 =
        (chain d b x (n+2)+2*z*x 0*x 2)+2*b (n+2)*x (n+2)*x (n+3)+d (n+3)*x (n+3)^2 := by
      rw [show n+1+2=(n+2)+1 by omega,chain]
      ring
    rw [he, ih]
    conv_rhs => rw [chain]
    simp only [reducedDiagonal,reducedOff]
    ring

theorem corrected_chain_pos (d b x : ℕ → ℝ) (z : ℝ) (n : ℕ)
    (hd : ∀ j ≤ n+3, 0 < bandDelta d b z j)
    (hx : ∃ j ≤ n+2, x j ≠ 0) :
    0 < chain d b x (n+2)+2*z*x 0*x 2 := by
  have hd0 : 0 < d 0 := by simpa [bandDelta] using hd 1 (by omega)
  rw [band_schur_identity d b x z (ne_of_gt hd0) n]
  have hsquare : 0 ≤ d 0*(x 0+b 0/d 0*x 1+z/d 0*x 2)^2 :=
    mul_nonneg (le_of_lt hd0) (sq_nonneg _)
  have hminor : ∀ j ≤ n+2, 0 < delta (reducedDiagonal d b z) (reducedOff d b z) j := by
    intro j hj
    rw [bandDelta_reduced d b z (ne_of_gt hd0)]
    exact div_pos (hd (j+1) (by omega)) hd0
  by_cases htail : ∃ j ≤ n+1, x (j+1) ≠ 0
  · exact add_pos_of_nonneg_of_pos hsquare (continuants_pos _ _ _ (n+1) hminor htail)
  · have hz : ∀ j ≤ n+1, x (j+1) = 0 := by simpa only [not_exists,not_and,not_not] using htail
    have hx0 : x 0 ≠ 0 := by
      rcases hx with ⟨j,hj,hx⟩
      rcases j with _ | j
      · exact hx
      · exact False.elim (hx (hz j (by omega)))
    have hchain : chain (reducedDiagonal d b z) (reducedOff d b z) (fun j => x (j+1)) (n+1) = 0 := by
      have hc : ∀ k ≤ n+1, chain (reducedDiagonal d b z) (reducedOff d b z) (fun j => x (j+1)) k = 0 := by
        intro k hk
        induction k with
        | zero => simp [chain,hz 0 (by omega)]
        | succ k ih => simp [chain,ih (by omega),hz (k+1) hk]
      exact hc (n+1) le_rfl
    rw [hchain,hz 0 (by omega),hz 1 (by omega)]
    simpa using mul_pos hd0 (sq_pos_of_ne_zero hx0)

noncomputable def correctedDiagonal (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 100*a 0
  | 1 => 100*a 2-2*a 2
  | n+2 => 100*a (2*(n+2))

theorem corrected_monomial_identity (a : ℕ → ℝ) (u : ℝ) (n : ℕ) :
    chain (correctedDiagonal a) (fun j => 50*a (2*j+1)) (fun j => u^j) (n+2)+2*a 2*1*u^2 =
      100*∑ k ∈ Finset.range (2*(n+2)+1), a k*u^k := by
  have he : ∀ m, chain (correctedDiagonal a) (fun j => 50*a (2*j+1)) (fun j => u^j) (m+1) =
      50*chain (fun j => 2*a (2*j)) (fun j => a (2*j+1)) (fun j => u^j) (m+1)-2*a 2*u^2 := by
    intro m
    induction m with
    | zero => simp [chain,correctedDiagonal]; ring
    | succ m ih =>
      rw [chain,ih]
      conv_rhs => rw [chain]
      simp only [correctedDiagonal]
      ring
  rw [show n+2=(n+1)+1 by omega,he,monomial_chain]
  ring

theorem corrected_power_polynomial_pos (a : ℕ → ℝ) (n : ℕ)
    (hd : ∀ j ≤ n+3, 0 < bandDelta (correctedDiagonal a) (fun j => 50*a (2*j+1)) (a 2) j)
    (u : ℝ) : 0 < ∑ k ∈ Finset.range (2*(n+2)+1), a k*u^k := by
  have h := corrected_chain_pos (correctedDiagonal a) (fun j => 50*a (2*j+1))
    (fun j => u^j) (a 2) n hd ⟨0, Nat.zero_le _, by simp⟩
  simp only [pow_zero] at h
  rw [corrected_monomial_identity] at h
  linarith

end R7.Core.Gram
