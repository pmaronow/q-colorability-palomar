module

public import ThLean.W.S336.ListSums

@[expose] public section

noncomputable section
open scoped BigOperators
namespace ThLean.W.S336
open ThresholdFoundations ThLean.BP.S3
attribute [local instance] Classical.propDecidable
universe u

private theorem splitListRec (h32 : S3_32Statement.{u}) (h34 : S3_34Statement.{u}) :
    ∀ (J : ℕ) (E : Type u) [Fintype E] [Nonempty E]
      (ν : E → ℝ) (label : E → Fin J) (z : ℝ),
      IsProbabilityVector ν → 0 ≤ z →
      (∀ j, 0 < cellMass ν label j) → ∀ ys : Fin J → List E,
      (∀ j, ∀ e ∈ ys j, label e = j) →
      weightedListMean z ν (fun w => indicator
        (∀ j, splitSublist label j w = ys j)) =
      ∏ j : Fin J, poissonListMass (z * cellMass ν label j)
        (fun e => ν e / cellMass ν label j) (ys j) := by
  intro J
  induction J with
  | zero =>
      intro E instE instN ν label z hν hz hcell ys hys
      exact Fin.elim0 (label (Classical.choice inferInstance))
  | succ n ih =>
      intro E instE instN ν label z hν hz hcell ys hys
      by_cases hn : n = 0
      · subst n
        have hlabel (e : E) : label e = 0 := by
          apply Fin.ext
          omega
        have hp : cellMass ν label (0 : Fin 1) = 1 := by
          simp [cellMass, hlabel, hν.2]
        have hevent (w : List E) :
            (∀ j : Fin 1, splitSublist label j w = ys j) ↔ w = ys 0 := by
          constructor
          · intro h
            simpa [splitSublist, hlabel] using h 0
          · intro hw
            subst w
            intro j
            have hj : j = 0 := by
              apply Fin.ext
              omega
            subst j
            simp [splitSublist, hlabel]
        have hmean : weightedListMean z ν (fun w => indicator
            (∀ j : Fin 1, splitSublist label j w = ys j)) =
            poissonListMass z ν (ys 0) := by
          rw [weightedListMean_eq_tsum h32 ν z hν hz
            (fun w => indicator (∀ j : Fin 1, splitSublist label j w = ys j))]
          · simp [hevent, indicator]
          · intro w
            unfold indicator
            split_ifs <;> norm_num
          · intro w
            unfold indicator
            split_ifs <;> norm_num
        rw [Fin.prod_univ_succ]
        simpa [hp] using hmean
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        let b : E → Bool := fun e => decide (label e = 0)
        let p : ℝ := cellMass ν label 0
        let r : ℝ := ∑ e : E, if b e then 0 else ν e
        let ν' : E → ℝ := fun e => if b e then 0 else ν e / r
        let label' : E → Fin n := fun e =>
          if he : label e = 0 then ⟨0, hnpos⟩ else ⟨(label e).val - 1, by
            have hv : (label e).val ≠ 0 := by
              intro hv
              apply he
              exact Fin.ext hv
            have hlt := (label e).isLt
            omega⟩
        let ys' : Fin n → List E := fun j => ys j.succ
        have hb_true (e : E) : b e = true ↔ label e = 0 := by
          simp [b]
        have hb_false (e : E) : b e = false ↔ label e ≠ 0 := by
          simp [b]
        have hpdef : (∑ e : E, if b e then ν e else 0) = p := by
          simp [p, cellMass, b]
        have hrdef : (∑ e : E, if b e then 0 else ν e) = r := rfl
        have hp : 0 < p := by
          exact hcell 0
        have hsumSplit : p + r = 1 := by
          calc
            p + r =
                (∑ e : E, if label e = 0 then ν e else 0) +
                  (∑ e : E, if label e = 0 then 0 else ν e) := by
              simp [p, r, cellMass, b]
            _ = ∑ e : E, ((if label e = 0 then ν e else 0) +
                  (if label e = 0 then 0 else ν e)) := by
              exact (Finset.sum_add_distrib (s := Finset.univ)
                (f := fun e : E => if label e = 0 then ν e else 0)
                (g := fun e : E => if label e = 0 then 0 else ν e)).symm
            _ = ∑ e : E, ν e := by
              apply Finset.sum_congr rfl
              intro e he
              by_cases h0 : label e = 0 <;> simp [h0]
            _ = 1 := hν.2
        have htailIndex : (⟨1, by omega⟩ : Fin (n+1)) ≠ 0 := by
          intro h
          have := congrArg Fin.val h
          simp at this
        have htailMassLe : cellMass ν label (⟨1, by omega⟩ : Fin (n+1)) ≤ r := by
          unfold cellMass r
          apply Finset.sum_le_sum
          intro e he
          by_cases hEq : label e = ⟨1, by omega⟩
          · have h0 : label e ≠ 0 := by rw [hEq]; exact htailIndex
            simp [hEq, (hb_false e).mpr h0]
          · by_cases h0 : label e = 0
            · simp [hEq, (hb_true e).mpr h0, hν.1 e]
            · simp [hEq, (hb_false e).mpr h0, hν.1 e]
        have hr : 0 < r := (hcell ⟨1, by omega⟩).trans_le htailMassLe
        have hν' : IsProbabilityVector ν' := by
          constructor
          · intro e
            by_cases hb : b e = true
            · simp [ν', hb]
            · simp [ν', hb, div_nonneg (hν.1 e) hr.le]
          · dsimp [ν']
            calc
              (∑ e : E, if b e then 0 else ν e/r) =
                  (∑ e : E, if b e then 0 else ν e)/r := by
                rw [Finset.sum_div]
                apply Finset.sum_congr rfl
                intro e he
                by_cases hb : b e = true <;> simp [hb]
              _ = r/r := by rw [hrdef]
              _ = 1 := div_self hr.ne'
        have hsucc (e : E) (he : label e ≠ 0) : label e = (label' e).succ := by
          apply Fin.ext
          have hval : (label e).val ≠ 0 := by
            intro hv
            apply he
            exact Fin.ext hv
          simp [label', he]
          omega
        have hmassTail (j : Fin n) :
            cellMass ν' label' j = cellMass ν label j.succ / r := by
          unfold cellMass
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro e he
          by_cases hzero : label e = 0
          · have hzeroSucc : label e ≠ j.succ := by
              intro hh
              rw [hzero] at hh
              exact (Fin.succ_ne_zero j) hh.symm
            change (if label' e = j then ν' e else 0) =
              (if label e = j.succ then ν e else 0)/r
            have hl : label' e = ⟨0, hnpos⟩ := by simp [label', hzero]
            have hνe : ν' e = 0 := by
              change (if b e then 0 else ν e/r) = 0
              simp [(hb_true e).mpr hzero]
            have hleft : (if label' e = j then ν' e else 0) = 0 := by
              by_cases hj : label' e = j <;> simp [hj, hνe]
            rw [hleft, if_neg hzeroSucc]
            simp
          · by_cases hj : label' e = j
            · have heq : label e = j.succ := by rw [hsucc e hzero, hj]
              have hνe : ν' e = ν e/r := by
                change (if b e then 0 else ν e/r) = ν e/r
                simp [(hb_false e).mpr hzero]
              change (if label' e = j then ν' e else 0) =
                (if label e = j.succ then ν e else 0)/r
              rw [if_pos hj, hνe, if_pos heq]
            · have hne : label e ≠ j.succ := by
                intro heq
                apply hj
                exact (Fin.succ_injective (n := n)) ((hsucc e hzero).symm.trans heq)
              have hνe : ν' e = ν e/r := by
                change (if b e then 0 else ν e/r) = ν e/r
                simp [(hb_false e).mpr hzero]
              change (if label' e = j then ν' e else 0) =
                (if label e = j.succ then ν e else 0)/r
              rw [if_neg hj, if_neg hne]
              simp
        have hcell' (j : Fin n) : 0 < cellMass ν' label' j := by
          rw [hmassTail]
          exact div_pos (hcell j.succ) hr
        have hys' : ∀ j : Fin n, ∀ e ∈ ys' j, label' e = j := by
          intro j e he
          have hlabel := hys j.succ e (by simpa [ys'] using he)
          have hne : label e ≠ 0 := by
            intro hz0
            rw [hlabel] at hz0
            exact (Fin.succ_ne_zero j) hz0
          have hs := hsucc e hne
          apply Fin.ext
          have hv := congrArg Fin.val (hs.symm.trans hlabel)
          simpa using hv
        have hfilterFirst (w : List E) : splitSublist label 0 w = w.filter b := by
          unfold splitSublist
          apply List.filter_congr
          intro e he
          simp [b]
        let getNo : List E → List E := fun w => w.filter (fun e => !b e)
        have hfilterTail (j : Fin n) (w : List E) :
            splitSublist label j.succ w = splitSublist label' j (getNo w) := by
          unfold splitSublist getNo
          rw [List.filter_filter]
          apply List.filter_congr
          intro e he
          by_cases hzero : label e = 0
          · have hb : b e = true := (hb_true e).mpr hzero
            have hzeroSucc : (0 : Fin (n+1)) ≠ j.succ := by
              intro hh
              exact (Fin.succ_ne_zero j) hh.symm
            simp [hzero, hb, hzeroSucc]
          · have hs := hsucc e hzero
            have hp : label e = j.succ ↔ label' e = j := by
              constructor
              · intro heq
                exact (Fin.succ_injective (n := n)) (hs.symm.trans heq)
              · intro heq
                rw [hs, heq]
            simp [hzero, (hb_false e).mpr hzero, hp]
        let Q : List E → Prop := fun v => ∀ j : Fin n,
          splitSublist label' j v = ys' j
        have hQfalse : ∀ v, Q v → ∀ e ∈ v, b e = false := by
          intro v hq e he
          let j := label' e
          have hem : e ∈ splitSublist label' j v := by
            simp [splitSublist, j, he]
          have heys : e ∈ ys (j.succ) := by
            have heys' : e ∈ ys' j := by
              rw [← hq j]
              exact hem
            simpa [ys'] using heys'
          have hlabel := hys j.succ e heys
          have hne : label e ≠ 0 := by
            intro hz0
            rw [hlabel] at hz0
            exact (Fin.succ_ne_zero j) hz0
          simp [b, hne]
        have hevent (w : List E) :
            (∀ j : Fin (n+1), splitSublist label j w = ys j) ↔
              (w.filter b = ys 0 ∧ Q (getNo w)) := by
          constructor
          · intro hall
            refine ⟨?_, ?_⟩
            · simpa [hfilterFirst] using hall 0
            · intro j
              simpa [Q, ys', hfilterTail] using hall j.succ
          · rintro ⟨hfirst, htail⟩
            intro j
            refine Fin.cases ?_ (fun j => ?_) j
            · simpa [hfilterFirst] using hfirst
            · simpa [hfilterTail, Q, ys'] using htail j
        have hsplit := weightedListMean_split_event h32 h34 ν b z p r
          hν hz hp hr hpdef hrdef (ys 0)
          (by intro e he; exact (hb_true e).mpr (hys 0 e he)) Q hQfalse
        have hrec := ih E ν' label' (z*r) hν' (mul_nonneg hz hr.le) hcell' ys' hys'
        have hrate (j : Fin n) :
            (z*r) * cellMass ν' label' j = z * cellMass ν label j.succ := by
          rw [hmassTail]
          field_simp [hr.ne']
        have hterm (j : Fin n) :
            poissonListMass ((z*r) * cellMass ν' label' j)
              (fun e => ν' e / cellMass ν' label' j) (ys' j) =
            poissonListMass (z * cellMass ν label j.succ)
              (fun e => ν e / cellMass ν label j.succ) (ys j.succ) := by
          have hmap : (ys' j).map (fun e => ν' e / cellMass ν' label' j) =
              (ys j.succ).map (fun e => ν e / cellMass ν label j.succ) := by
            apply List.map_congr_left
            intro e he
            have heLabel := hys j.succ e (by simpa [ys'] using he)
            have hνe : ν' e = ν e/r := by
              have hne : label e ≠ 0 := by
                intro hzero
                rw [heLabel] at hzero
                exact (Fin.succ_ne_zero j) hzero
              change (if b e then 0 else ν e/r) = ν e/r
              simp [(hb_false e).mpr hne]
            rw [hνe, hmassTail]
            field_simp [hr.ne', (hcell j.succ).ne']
          unfold poissonListMass
          rw [hrate]
          congr 1
          exact congrArg List.prod hmap
        have htailProd :
            (∏ j : Fin n, poissonListMass ((z*r) * cellMass ν' label' j)
              (fun e => ν' e / cellMass ν' label' j) (ys' j)) =
            (∏ j : Fin n, poissonListMass (z * cellMass ν label j.succ)
              (fun e => ν e / cellMass ν label j.succ) (ys j.succ)) := by
          apply Finset.prod_congr rfl
          intro j hj
          exact hterm j
        have hmain : weightedListMean z ν (fun w => indicator
            (∀ j : Fin (n+1), splitSublist label j w = ys j)) =
            poissonListMass (z*p) (fun e => ν e/p) (ys 0) *
              weightedListMean (z*r) ν' (fun v => indicator (Q v)) := by
          calc
            _ = weightedListMean z ν (fun w => indicator
                  (w.filter b = ys 0 ∧ Q (getNo w))) := by
                congr 1
                funext w
                exact congrArg indicator (propext (hevent w))
            _ = _ := hsplit
        calc
          weightedListMean z ν (fun w => indicator
              (∀ j : Fin (n+1), splitSublist label j w = ys j)) =
              poissonListMass (z*p) (fun e => ν e/p) (ys 0) *
                ∏ j : Fin n, poissonListMass ((z*r) * cellMass ν' label' j)
                  (fun e => ν' e / cellMass ν' label' j) (ys' j) := by
            rw [hmain, hrec]
          _ = ∏ j : Fin (n+1), poissonListMass (z * cellMass ν label j)
                (fun e => ν e / cellMass ν label j) (ys j) := by
            rw [Fin.prod_univ_succ]
            simpa [p, Fin.succ_zero_eq_one] using congrArg
              (fun x => poissonListMass (z*p) (fun e => ν e/p) (ys 0) * x) htailProd

theorem S3_35aStatement_of_deps (h32 : S3_32Statement.{u})
    (h34 : S3_34Statement.{u}) : S3_35aStatement.{u} := by
  intro E instE instN ν J label z hν hz hcell ys hys
  exact splitListRec h32 h34 J E ν label z hν hz hcell ys hys

end ThLean.W.S336
