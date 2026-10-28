import ThLean.BP.S3.Poisson

universe u

namespace ThLean.Contrib.S340

/-- Remaining core of S3-37a: the point-mass factorization for the joint
output (two induced multigraphs and all cross-block neighbor lists) of a
Poisson word on the pair alphabet. This is intentionally a transparent node;
it is the pushforward-and-sum step not yet derived from the splitting leaves. -/
def S3_37aCoreStatement : Prop :=
  ThLean.BP.S3.S3_37aStatement.{u}

end ThLean.Contrib.S340
