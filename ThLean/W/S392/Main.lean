import ThLean.W.S392.EdgeCount

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S392
open ThresholdFoundations

private theorem support_of_positive_pair {V : Type u} [Fintype V]
    (G : MGraph V) {a b : V} (h : 0 < G (s(a,b))) :
    a ∈ vertexSupport G ∧ b ∈ vertexSupport G := by
  constructor
  · simp [vertexSupport]
    exact ⟨s(a,b), h, b, rfl⟩
  · simp [vertexSupport]
    exact ⟨s(a,b), h, a, by rw [Sym2.eq_swap]⟩

private theorem induced_loopless {V : Type u} [Fintype V]
    (G : MGraph V) (hG : Loopless G) :
    Loopless (inducedGraph G (vertexSupport G)) := by
  intro x
  change G (Sym2.map Subtype.val (s(x,x))) = 0
  simpa using hG x.val

private theorem induced_colorable_iff {V : Type u} [Fintype V] (q : ℕ)
    (hq : 3 ≤ q) (G : MGraph V) :
    (Colorable q G ↔ Colorable q (inducedGraph G (vertexSupport G))) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨fun x => σ x.val, ?_⟩
    intro x y hxy
    apply hσ x.val y.val
    simpa [inducedGraph, Sym2.map_mk] using hxy
  · rintro ⟨τ, hτ⟩
    let σ : V → Fin q := fun a => if ha : a ∈ vertexSupport G then τ ⟨a, ha⟩ else ⟨0, by omega⟩
    refine ⟨σ, ?_⟩
    intro a b hab
    obtain ⟨ha,hb⟩ := support_of_positive_pair G hab
    have hp : 0 < (inducedGraph G (vertexSupport G)) (s(⟨a,ha⟩,⟨b,hb⟩)) := by
      simpa [inducedGraph, Sym2.map_mk] using hab
    dsimp [σ]
    rw [dif_pos ha, dif_pos hb]
    exact hτ ⟨a,ha⟩ ⟨b,hb⟩ hp

theorem S3_57bStatement_holds
    (hc : ThLean.Contrib.S392.S3_57bConnectedStatement.{u})
    (hθ : ThLean.Contrib.S392.S3_57bThetaStatement.{u})
    (hd : ThLean.Contrib.S392.S3_57bDumbbellStatement.{u}) :
    ThLean.BP.S3.S3_57bStatement.{u} := by
  intro V _ q hq G hloop hconn hsize
  let S := vertexSupport G
  have hloop' : Loopless (inducedGraph G S) := by
    simpa [S] using induced_loopless G hloop
  have hconn' : (ThLean.BP.S3.graphSupport (inducedGraph G S)).Connected := by
    simpa [S] using hc V G hconn
  have hedge : edgeCount (inducedGraph G S) = edgeCount G := by
    simpa [S] using S3_57bEdgeCount_proved G
  have hcolor : Colorable q G ↔ Colorable q (inducedGraph G S) := by
    simpa [S] using induced_colorable_iff q hq G
  exact ⟨hloop', hconn', hedge, hcolor,
    (by simpa [S] using hθ V G), (by simpa [S] using hd V G)⟩

end ThLean.W.S392
