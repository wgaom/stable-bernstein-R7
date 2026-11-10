import R7.Algebra.IntegerExpression
import Mathlib.Data.List.Sort

namespace R7.Core.SpectralCoefficient.Kronecker.Reduced.Sort
abbrev Terms := R7.Algebra.Kronecker.Terms
def desc (a b : ℕ × ℤ) : Bool := Nat.ble b.1 a.1
def Sorted (ts : Terms) : Prop := ts.Pairwise (fun a b => b.1 ≤ a.1)
def RunsSorted (xss : List Terms) : Prop := ∀ xs∈xss, Sorted xs

def mergeF : ℕ → Terms → Terms → Terms
  | 0,xs,ys => xs++ys
  | n+1,xs,ys => match xs,ys with
    | [],ys => ys
    | xs,[] => xs
    | x::xs,y::ys => bif desc x y then x::mergeF n xs (y::ys)
        else y::mergeF n (x::xs) ys

theorem mergeF_eq (n : ℕ) (xs ys : Terms) (h : xs.length+ys.length≤n) :
    mergeF n xs ys=List.merge xs ys desc := by
  induction n generalizing xs ys with
  | zero =>
    have hx : xs=[] := List.length_eq_zero_iff.mp (by omega)
    have hy : ys=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs; subst ys; simp [mergeF]
  | succ n ih =>
    cases xs with
    | nil => simp [mergeF]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeF]
      | cons y ys =>
        change (bif desc x y then x::mergeF n xs (y::ys) else y::mergeF n (x::xs) ys)=_
        rw [List.merge]
        split <;> rename_i hc
        · simp only [hc,cond_true]
          congr 1
          exact ih xs (y::ys) (by simp only [List.length_cons] at h ⊢; omega)
        · simp only [hc,cond_false]
          congr 1
          exact ih (x::xs) ys (by simp only [List.length_cons] at h ⊢; omega)

def merge (xs ys : Terms) : Terms := mergeF (xs.length+ys.length) xs ys

theorem merge_eq (xs ys : Terms) : merge xs ys=List.merge xs ys desc :=
  mergeF_eq _ _ _ (le_refl _)

def pairs : List Terms → List Terms
  | [] => []
  | [xs] => [xs]
  | xs::ys::rest => merge xs ys :: pairs rest

def rounds : ℕ → List Terms → List Terms
  | 0,xss => xss
  | n+1,xss => pairs (rounds n xss)

def finish (xss : List Terms) : Terms :=
  xss.foldr (fun xs ys => merge xs ys) []

def sort (ts : Terms) : Terms := finish (rounds 10 (ts.map (fun a => [a])))

theorem sorted_merge (xs ys : Terms) (hx : Sorted xs) (hy : Sorted ys) :
    Sorted (merge xs ys) := by
  rw [merge_eq]
  have ht : ∀ a b c, desc a b=true → desc b c=true → desc a c=true := by
    intro a b c hab hbc
    simp only [desc,Nat.ble_eq] at *
    omega
  have hall : ∀ a b, (desc a b || desc b a)=true := by
    intro a b
    simp only [Bool.or_eq_true,desc,Nat.ble_eq]
    omega
  have hh := List.pairwise_merge ht hall xs ys
    (by simpa only [desc,Nat.ble_eq] using hx)
    (by simpa only [desc,Nat.ble_eq] using hy)
  simpa only [Sorted,desc,Nat.ble_eq] using hh

theorem pairs_sorted : ∀ xss, RunsSorted xss → RunsSorted (pairs xss)
  | [],_ => by simp [RunsSorted,pairs]
  | [xs],h => h
  | xs::ys::rest,h => by
    intro zs hz
    simp only [pairs,List.mem_cons] at hz
    rcases hz with hz|hz
    · subst zs
      exact sorted_merge xs ys (h xs (by simp)) (h ys (by simp))
    · exact pairs_sorted rest (fun us hu => h us (by simp [hu])) zs hz

theorem rounds_sorted (n : ℕ) (xss : List Terms) (h : RunsSorted xss) :
    RunsSorted (rounds n xss) := by
  induction n with
  | zero => exact h
  | succ n ih => exact pairs_sorted _ ih

theorem finish_sorted (xss : List Terms) (h : RunsSorted xss) : Sorted (finish xss) := by
  induction xss with
  | nil => exact List.Pairwise.nil
  | cons xs rest ih =>
    exact sorted_merge xs (finish rest) (h xs (by simp)) (ih (fun us hu => h us (by simp [hu])))

theorem sort_sorted (ts : Terms) : Sorted (sort ts) := by
  apply finish_sorted
  apply rounds_sorted
  intro xs hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  simp [Sorted]

theorem pairs_perm : ∀ xss, (pairs xss).flatten.Perm xss.flatten
  | [] => .refl _
  | [xs] => .refl _
  | xs::ys::rest => by
    simpa only [pairs,List.flatten_cons,List.append_assoc,merge_eq] using
      (List.Perm.append (List.merge_perm_append (le := desc) (xs := xs) (ys := ys))
        (pairs_perm rest))

theorem rounds_perm (n : ℕ) (xss : List Terms) : (rounds n xss).flatten.Perm xss.flatten := by
  induction n with
  | zero => exact .refl _
  | succ n ih => exact (pairs_perm _).trans ih

theorem finish_perm (xss : List Terms) : (finish xss).Perm xss.flatten := by
  induction xss with
  | nil => exact .refl _
  | cons xs rest ih =>
    simpa only [finish,List.foldr_cons,merge_eq] using
      (List.merge_perm_append (le := desc) (xs := xs) (ys := finish rest)).trans
        (List.Perm.append (.refl xs) ih)

theorem sort_perm (ts : Terms) : (sort ts).Perm ts := by
  have hh := (finish_perm _).trans (rounds_perm 10 (ts.map (fun a => [a])))
  have hs : (ts.map (fun a => [a])).flatten=ts := by
    clear hh
    induction ts <;> simp_all
  simpa only [sort,hs] using hh

end R7.Core.SpectralCoefficient.Kronecker.Reduced.Sort
