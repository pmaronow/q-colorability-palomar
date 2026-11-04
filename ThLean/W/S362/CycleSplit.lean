module

public import ThLean.W.S362.CycleArcs

@[expose] public section

noncomputable section
namespace ThLean.W.S362
open ThresholdFoundations


theorem S3_59Statement_holds : ThLean.BP.S3.S3_59Statement := by
  classical
  intro V _ G c a b ha hb hab
  rcases Finset.mem_image.mp ha with ⟨ia, -, hia⟩
  let d := rotateCycle c ia
  have hd0 : d.vertex (zeroFin c.length (cycleLen_pos c)) = a := by
    change c.vertex (rotateIdx c ia (zeroFin c.length (cycleLen_pos c))) = a
    rw [← hia]
    apply congrArg c.vertex
    apply Fin.ext
    simp [rotateIdx, zeroFin, Nat.mod_eq_of_lt ia.isLt]
  have hbd : b ∈ cycleVertices d := by
    simpa [d, rotateCycle_vertices c ia] using hb
  have hd0d : d.vertex (zeroFin d.length (cycleLen_pos d)) = a := by
    simpa [d, rotateCycle] using hd0
  rcases Finset.mem_image.mp hbd with ⟨k, -, hkb⟩
  have hkpos : 0 < k.val := by
    by_contra hk
    have hkval : k.val = 0 := by omega
    have hk0 : k = zeroFin c.length (cycleLen_pos c) := by
      apply Fin.ext
      simpa [zeroFin] using hkval
    apply hab
    calc
      a = d.vertex (zeroFin c.length (cycleLen_pos c)) := hd0.symm
      _ = d.vertex k := by rw [hk0]
      _ = b := hkb
  let p := arcForward d k
  let q := arcWrap d k hkpos
  let r := reversePath q
  have hpfrom : PathFrom p a b := by
    simpa [p, hd0d, hkb] using arcForward_from d k
  have hqfrom : PathFrom q b a := by
    simpa [q, hd0d, hkb] using arcWrap_from d k hkpos
  have hrfrom : PathFrom r a b := by
    exact reversePath_from q b a hqfrom
  have hdisj : Disjoint (pathOccurrences p) (pathOccurrences r) := by
    dsimp [p, r, q]
    rw [pathOccurrences_reverse]
    exact arc_occ_disjoint d k hkpos
  have hunion : pathOccurrences p ∪ pathOccurrences r = cycleOccurrences c := by
    dsimp [p, r, q]
    rw [pathOccurrences_reverse, arc_occ_union, rotateCycle_occurrences]
  have hinter : pathVertices p ∩ pathVertices r = {a,b} := by
    dsimp [p, r, q]
    rw [pathVertices_reverse, arc_vertex_inter]
    simpa [hd0d, hkb]
  refine ⟨p, r, ?_, ?_, hpfrom, hrfrom, hdisj, hunion, hinter, ?_⟩
  · dsimp [p]
    exact arcForward_pos d k hkpos
  · dsimp [r, q]
    exact arcWrap_pos d k hkpos
  · dsimp [p, r, q]
    simpa [reversePath, d, rotateCycle] using arc_lengths d k hkpos

end ThLean.W.S362
