module

public import ThLean.W.S370S.Lists

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S370S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u}

theorem codeLabel_eq {k : ℕ} (hk : 0 < k) (v : Fin k → V) {i : ℕ} (hi : i < k) :
    codeLabel hk v i = v ⟨i, hi⟩ := by
  simp [codeLabel, Nat.mod_eq_of_lt hi]

theorem map_range_eq_ofFn {n : ℕ} (g : ℕ → V) (f : Fin n → V)
    (h : ∀ i, g i.val = f i) :
    (List.range n).map g = List.ofFn f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa using h ⟨i, by simpa using hj⟩

theorem cons_range_eq_ofFn {n : ℕ} (hn : 0 < n) (a : V)
    (g : ℕ → V) (f : Fin n → V) (h0 : f ⟨0, hn⟩ = a)
    (hs : ∀ i : Fin (n-1), f ⟨i.val+1, by omega⟩ = g i.val) :
    [a] ++ (List.range (n-1)).map g = List.ofFn f := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    have hin : i < n := by simpa using hj
    cases i with
    | zero => simpa using h0.symm
    | succ i => simpa using (hs ⟨i, by omega⟩).symm

theorem cons_range_append_eq_ofFn {n : ℕ} (hn : 0 < n) (a b : V)
    (g : ℕ → V) (f : Fin (n+1) → V) (h0 : f 0 = a) (hn' : f (Fin.last n) = b)
    (hs : ∀ i : Fin (n-1), f ⟨i.val+1, by omega⟩ = g i.val) :
    ([a] ++ (List.range (n-1)).map g) ++ [b] = List.ofFn f := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    have hin : i < n+1 := by simpa using hj
    by_cases hlast : i = n
    · subst i
      rw [List.getElem_append_right (by simp; omega)]
      simpa only [List.length_append, List.length_cons, List.length_nil,
        List.length_map, List.length_range, Nat.add_zero,
        show n-(1+(n-1))=0 by omega, List.getElem_cons_zero, List.getElem_ofFn,
        Fin.last] using hn'.symm
    · rw [List.getElem_append_left (by simp; omega)]
      cases i with
      | zero => simpa using h0.symm
      | succ i => simpa using (hs ⟨i, by omega⟩).symm

theorem codeLabel_window {k n : ℕ} (hk : 0 < k) (v : Fin k → V)
    (a : ℕ) (ha : a+n ≤ k) :
    (List.range n).map (fun i => codeLabel hk v (a+i)) =
      List.ofFn (fun i : Fin n => v ⟨a+i.val, by omega⟩) := by
  apply map_range_eq_ofFn
  intro i
  exact codeLabel_eq hk v (by omega)

end ThLean.W.S370S
