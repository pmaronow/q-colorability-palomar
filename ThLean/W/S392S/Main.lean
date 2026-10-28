import ThLean.W.S392S.Lift
import ThLean.W.S392.EdgeCount

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S392S
open ThresholdFoundations
open ThLean.BP.S3 (graphSupport)

private theorem support_of_positive_pair {V : Type u} [Fintype V]
    (G : MGraph V) {a b : V} (h : 0 < G (s(a,b))) :
    a ∈ vertexSupport G ∧ b ∈ vertexSupport G := by
  constructor
  · simp [vertexSupport]
    exact ⟨s(a,b), h, b, rfl⟩
  · simp [vertexSupport]
    exact ⟨s(a,b), h, a, by rw [Sym2.eq_swap]⟩

/-- Traverse an occurrence path inside the subtype of supported vertices. -/
private theorem supported_path_reachable {V : Type u} [Fintype V]
    (G : MGraph V) {a b : V} (ha : a ∈ vertexSupport G) (hb : b ∈ vertexSupport G)
    (p : OccurrencePath G) (hp : PathFrom p a b) :
    (graphSupport (inducedGraph G (vertexSupport G))).Reachable ⟨a,ha⟩ ⟨b,hb⟩ := by
  have reach : ∀ k (hk : k ≤ p.length),
      ∃ hs : p.vertex ⟨k, by omega⟩ ∈ vertexSupport G,
        (graphSupport (inducedGraph G (vertexSupport G))).Reachable
          ⟨a,ha⟩ ⟨p.vertex ⟨k, by omega⟩,hs⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hs : p.vertex ⟨0, by omega⟩ ∈ vertexSupport G := by
        rw [hp.1]
        exact ha
      refine ⟨hs, ?_⟩
      have heq : (⟨p.vertex ⟨0, by omega⟩,hs⟩ : {v // v ∈ vertexSupport G}) =
          ⟨a,ha⟩ := Subtype.ext hp.1
      rw [heq]
    | succ k ih =>
      intro hk
      obtain ⟨hs, hr⟩ := ih (by omega)
      let i : Fin p.length := ⟨k, by omega⟩
      have hpos : 0 < G (s(p.vertex ⟨k, by omega⟩, p.vertex ⟨k+1, by omega⟩)) := by
        rw [← p.joins i]
        exact Nat.zero_lt_of_lt (p.edge i).2.isLt
      obtain ⟨_, hs'⟩ := support_of_positive_pair G hpos
      refine ⟨hs', hr.trans (SimpleGraph.Adj.reachable ?_)⟩
      constructor
      · intro heq
        have hi := p.vertex_injective (congrArg Subtype.val heq)
        have hiNat : k = k+1 := congrArg Fin.val hi
        exact (Nat.lt_succ_self k).ne hiNat
      · change 0 < G (Sym2.map Subtype.val (s(_, _)))
        simpa only [Sym2.map_mk] using hpos
  obtain ⟨hs, hr⟩ := reach p.length le_rfl
  have heq : (⟨p.vertex ⟨p.length, by omega⟩,hs⟩ : {v // v ∈ vertexSupport G}) =
      ⟨b,hb⟩ := Subtype.ext hp.2
  rw [heq] at hr
  exact hr

theorem induced_connected {V : Type u} [Fintype V] (G : MGraph V)
    (hconn : ConnectedSupport G) (hne : (vertexSupport G).Nonempty) :
    (graphSupport (inducedGraph G (vertexSupport G))).Connected := by
  obtain ⟨v, hv⟩ := hne
  letI : Nonempty {v // v ∈ vertexSupport G} := ⟨⟨v, hv⟩⟩
  refine ⟨?_⟩
  intro a b
  obtain ⟨p, hp⟩ := hconn a.val a.property b.val b.property
  exact supported_path_reachable G a.property b.property p hp

private theorem induced_loopless {V : Type u} [Fintype V]
    (G : MGraph V) (hG : Loopless G) :
    Loopless (inducedGraph G (vertexSupport G)) := by
  intro x
  change G (Sym2.map Subtype.val (s(x,x))) = 0
  simpa using hG x.val

private theorem induced_colorable_iff {V : Type u} [Fintype V] (q : ℕ)
    (hq : 3 ≤ q) (G : MGraph V) :
    Colorable q G ↔ Colorable q (inducedGraph G (vertexSupport G)) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨fun x => σ x.val, ?_⟩
    intro x y hxy
    apply hσ x.val y.val
    simpa [inducedGraph, Sym2.map_mk] using hxy
  · rintro ⟨τ, hτ⟩
    let σ : V → Fin q := fun a =>
      if ha : a ∈ vertexSupport G then τ ⟨a, ha⟩ else ⟨0, by omega⟩
    refine ⟨σ, ?_⟩
    intro a b hab
    obtain ⟨ha,hb⟩ := support_of_positive_pair G hab
    have hp : 0 < (inducedGraph G (vertexSupport G)) (s(⟨a,ha⟩,⟨b,hb⟩)) := by
      simpa [inducedGraph, Sym2.map_mk] using hab
    dsimp [σ]
    rw [dif_pos ha, dif_pos hb]
    exact hτ ⟨a,ha⟩ ⟨b,hb⟩ hp

theorem S3_57bStatement_holds : ThLean.BP.S3.S3_57bStatement.{u} := by
  intro V _ q hq G hloop hconn hsize
  refine ⟨induced_loopless G hloop, ?_, ThLean.W.S392.S3_57bEdgeCount_proved G,
    induced_colorable_iff q hq G, thetaIn_lift, dumbbellIn_lift⟩
  exact induced_connected G hconn (Finset.card_pos.mp (by omega))

example : ThLean.BP.S3.S3_57bStatement.{u} := S3_57bStatement_holds

end ThLean.W.S392S
