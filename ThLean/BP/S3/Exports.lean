import ThLean.BP.S3.Adapters

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations


/-! Exact exports of the frozen Section 3 interface. -/

theorem PreFiniteLaws_of_S3 (h2 : S3_02Statement.{u})
    (hb : S3_02bStatement.{u,v}) (h3 : S3_03aStatement.{u}) :
    ThresholdFoundations.PreFiniteLawsStatement.{u,v} := by
  refine ⟨hb.1,hb.2,?_,?_⟩
  · intro V _ hV r m hrm f
    letI : Nonempty (Pair V) := Fintype.card_pos_iff.mp (h3 V hV).2.1
    let i : Fin r ↪ Fin m := ⟨fun j => ⟨j.val, lt_of_lt_of_le j.isLt hrm⟩,
      by intro a b h; apply Fin.ext; exact congrArg (fun z : Fin m => z.val) h⟩
    change uniformMean (fun x : EdgeTuple V m => f (fun j : Fin r => x (i j))) = _
    exact (h2 (Pair V) m r i).2.2.1 f
  · intro V _ hV r m hrm f
    letI : Nonempty (Pair V) := Fintype.card_pos_iff.mp (h3 V hV).2.1
    let i : Fin r ↪ Fin m := ⟨fun j => ⟨j.val, lt_of_lt_of_le j.isLt hrm⟩,
      by intro a b h; apply Fin.ext; exact congrArg (fun z : Fin m => z.val) h⟩
    change uniformMeanENN (fun x : EdgeTuple V m => f (fun j : Fin r => x (i j))) = _
    exact (h2 (Pair V) m r i).2.1 f

theorem PreFrozen_of_S3 (h9 : S3_09bStatement.{u,u})
    (h10 : S3_10Statement.{u}) (h11 : S3_11Statement.{u})
    (h12 : S3_12Statement.{u}) : ThresholdFoundations.PreFrozenStatement.{u} := by
  intro V _ q hq hV
  have hq2 : 2 ≤ q := by omega
  refine ⟨(h10 V q hq2 hV).1,(h10 V q hq2 hV).2.1,
    (h9 V V q hq2).1,?_,?_⟩
  · intro G hG
    simpa [indicator,hG] using (h11 V q hq2 hV).2 G
  · intro G _ C hC
    exact ((h12 V q hq2 hV).1 G C hC).2

theorem PreHazard_of_S3 (h15 : S3_15bStatement.{0}) (h16 : S3_16bStatement.{0}) :
    ThresholdFoundations.PreHazardStatement := by
  intro q n hq hn
  have hq2 : 2 ≤ q := by omega
  have hn' : 2 ≤ Fintype.card (Fin n) := by simpa using hn
  exact ⟨h15 (Fin n) q hq2 hn', (h16 (Fin n) q hq2 hn').1,
    (h16 (Fin n) q hq2 hn').2⟩

theorem PreTerminal_of_S3 (h17 : S3_17Statement.{0})
    (h2 : S3_02cStatement.{u}) (h20 : S3_02cStatement.{0})
    (h19 : S3_19bStatement.{u}) : ThresholdFoundations.PreTerminalStatement.{u} := by
  constructor
  · intro q n hq hn A h L U
    have hn' : 2 ≤ Fintype.card (Fin n) := by simpa using hn
    unfold ThresholdFoundations.terminalRangeENN
    apply tsum_congr
    intro m
    split_ifs
    · rw [(h17 (Fin n) q (by omega) hn' A).1 m (h m)]
      congr 1
      funext G
      rw [h20 (Fin n) hn' q A G]
    · rfl
  · intro V _ q hq hV A h w hA hadm hInv hw _ e
    have he := h19 V q (by omega) hV A h w hadm hA hInv hw e
    simpa only [graphLawMeanENN, h2 V hV q A] using he

theorem PreLifetime_of_S3 (h21 : S3_21Statement.{u}) (h22 : S3_22Statement.{u,u})
    (h26 : S3_26bStatement.{u}) (h27 : S3_27bStatement.{u}) (h28 : S3_28bStatement.{u}) :
    ThresholdFoundations.PreLifetimeStatement.{u} := by
  intro V _ q hq hV
  have hq2 : 2 ≤ q := by omega
  have h := h21 V q hq2 hV
  refine ⟨?_,?_,h27 V q hq2 hV,h28 V q hq2 hV⟩
  · intro G _
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro hG
      exact ⟨(h.2.2.1 G hG).1,(h.2.2.1 G hG).2.1⟩
    · intro b
      have hb := h.2.2.2.1 G b
      exact ⟨hb.1,hb.2.2,hb.2.1⟩
    · intro b b' hbb
      exact (h.2.2.2.2.2 G).1 hbb
    · intro hG b hb
      exact (h.2.2.2.2.1 G hG).1 b hb
    · intro hn
      exact h26 V q hq2 hn G
  · intro G G' hGG
    exact ((h22 V V q hq2 hV hV).1 G G' hGG).2

theorem PreRelabel_of_S3 (h : S3_01bStatement.{u,v}) :
    ThresholdFoundations.PreRelabelStatement.{u,v} := h

theorem PreClassmass_of_S3 (h30 : S3_30bStatement.{u}) (h26 : S3_26Statement.{u}) :
    ThresholdFoundations.PreClassmassStatement.{u} := by
  intro V _ q hq hn G _ hG y hy hyl
  have hq2 : 2 ≤ q := by omega
  have hfin := ((h26 V q hq2 hn).2.1 G).1
  have hyr : y < lifetimeReal q G :=
    (ENNReal.ofReal_lt_iff_lt_toReal hy.le hfin).1 hyl
  have h := (h30 V q hq2 hn G hG).2.2.2 y hy hyr
  exact ⟨h.2.1.le,h.2.2⟩

theorem PreQuantile_of_S3 (h5 : S3_05Statement.{0}) (h6 : S3_06bStatement.{0})
    (h7 : S3_07bStatement.{0}) : ThresholdFoundations.PreQuantileStatement := by
  intro q n M hq hn η hη0 hη1
  have hn' : 2 ≤ Fintype.card (Fin n) := by simpa using hn
  have hq2 : 2 ≤ q := by omega
  have a := h5 (Fin n) q M hq2 hn'
  have b := h6 (Fin n) q M η hn' hη0 hη1
  have c := h7 (Fin n) q M η hq2 hn' hη0 hη1
  exact ⟨c.1,c.2.1,b.2.2.1,b.2.2.2.1,a.2.2.1,a.2.2.2.1,c.2.2.2.1,c.2.2.2.2.1⟩

theorem PrePoisson_of_S3 (h31 : S3_31Statement) (h40 : S3_40Statement)
    (h41 : S3_41aStatement) : ThresholdFoundations.PrePoissonStatement.{u} := by
  refine ⟨?_,?_,h40⟩
  · intro z hz
    exact ⟨(h31 z hz).2.1,(h31 z hz).2.2.1,(h31 z hz).1⟩
  · intro V _ _ h p hp
    exact h41 (fun m => graphMeanENN m h) p hp

theorem PreSplitLists_of_S3 (h35 : S3_35aStatement.{u}) :
    ThresholdFoundations.PreSplitListsStatement.{u} := by
  intro E _ J _ ν label z hν hsum hz ys hys hpos
  haveI : Nonempty E := by
    by_contra h
    haveI : IsEmpty E := not_nonempty_iff.mp h
    simp at hsum
  exact h35 E ν J label z ⟨hν,hsum⟩ hz hpos ys hys

theorem PreSplitGraph_of_S3 (h : S3_37cStatement.{u,v}) :
    ThresholdFoundations.PreSplitGraphStatement.{u,v} := h
theorem PreSplitRoot_of_S3 (h : S3_38cStatement.{u}) :
    ThresholdFoundations.PreSplitRootStatement.{u} := h
theorem PreSplit_of_S3 (h35 : S3_35aStatement.{u}) (h37 : S3_37cStatement.{u,v})
    (h38 : S3_38cStatement.{u}) (h36 : S3_36bStatement.{u}) :
    ThresholdFoundations.PreSplitStatement.{u,v} :=
  ⟨PreSplitLists_of_S3 h35,h37,h38,h36⟩

theorem PreTails_of_S3 (h43 : S3_43Statement) (h47 : S3_47Statement)
    (h48 : S3_48Statement) (h49 : S3_49Statement) (h50 : S3_50Statement) :
    ThresholdFoundations.PreTailsStatement := by
  refine ⟨?_,?_,?_,?_⟩
  · intro m _ p hp0 hp1 k hk
    exact h43 m k p hk hp0 hp1
  · intro z k hz hk
    exact h47 z k hz hk
  · intro z s hz hs
    exact ⟨h48 z s hz hs,h49 z s hz hs⟩
  · intro z hz i hi
    exact (h50 z i hz hi).1

theorem PreCycles_of_S3 (h57 : S3_57Statement.{u}) (h63 : S3_63aStatement.{u})
    (hb : S3_57bStatement.{u}) : ThresholdFoundations.PreCyclesStatement.{u} := by
  intro V _ q hq G hG hconn hsize
  let S := vertexSupport G
  obtain ⟨hl,hc,he,hcol,hθ,hd⟩ := hb V q hq G hG hconn hsize
  have hn : 2 ≤ Fintype.card {v : V // v ∈ S} := by simpa [S] using hsize
  constructor
  · intro hcount
    apply hcol.mpr
    apply h57 {v : V // v ∈ S} q hq hn (inducedGraph G S) hl hc
    simpa only [Fintype.card_coe,S,he] using hcount
  · intro hcount
    have hcount' : Fintype.card {v : V // v ∈ S} + 1 ≤ edgeCount (inducedGraph G S) := by
      simpa only [Fintype.card_coe,S,he] using hcount
    rcases h63 {v : V // v ∈ S} hn (inducedGraph G S) hl hc hcount' with h | h
    · exact Or.inl (hθ h)
    · exact Or.inr (hd h)

theorem PreCentre_of_S3 (h52 : S3_52Statement) (h53 : S3_53Statement)
    (h73 : S3_73Statement) (h74 : S3_74Statement.{0}) (h75 : S3_75Statement) :
    ThresholdFoundations.PreCentreStatement := by
  intro q hq Λ hΛ η hη0 hη1
  refine ⟨(fun β hβ n hn => (h52 q (by omega)).2.2.2.1 β n hβ hn),?_,?_⟩
  · intro β hβ
    obtain ⟨N,hN⟩ := h53 q Λ η β hq hΛ hη0 hη1 hβ
    apply Filter.eventually_atTop.2
    refine ⟨max N (2*q),?_⟩
    intro n hn
    have h := hN n ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
    exact ⟨h.1,(Nat.cast_le.mpr h.2.1).trans h.2.2.1,h.2.2.2⟩
  · intro c hc0 hc1
    have hC := (h73 c 2 0 hc0 hc1 (by omega) (by simpa using (mul_nonneg hc0.le (show (0 : ℝ) ≤ 2 by norm_num)))).2.2.2
    refine ⟨obstructionConstant c,hC,?_,?_⟩
    · intro n hn
      have hn' : 2 ≤ Fintype.card (Fin n) := by simpa using (show 2 ≤ n by omega)
      have hf : (Nat.floor (c*n) : ℝ) ≤ c*Fintype.card (Fin n) := by
        simpa using (Nat.floor_le (show 0 ≤ c*n by positivity))
      simpa using h74 (Fin n) q hq hn' c (Nat.floor (c*n)) hc0 hc1 hf
    · obtain ⟨N,hN⟩ := h75 q Λ η c hq hΛ hη0 hη1 hc0 hc1
      apply Filter.eventually_atTop.2
      refine ⟨max N (2*q),?_⟩
      intro n hn
      exact hN n ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)

theorem PreStopping_of_S3 (h4 : S3_04aStatement.{u})
    (hc : S3_04cStatement.{u}) (hd : S3_04dStatement.{u}) :
    ThresholdFoundations.PreStoppingStatement.{u} := by
  intro V _ hV
  refine ⟨hc V hV,?_,(hd V hV).1,(hd V hV).2⟩
  intro q hq
  exact (h4 V q (by omega)).2.2.1

end ThLean.BP.S3
