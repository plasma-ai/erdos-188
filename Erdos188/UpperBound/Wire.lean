module

public import Erdos188.UpperBound.Families

/-!
# Wire representation of sites

Shared integer encoding of a rational site for the finite certificate bridge.
Both the covering and the safety checkers consume this structure; the six
integers are divided as rationals to recover the semantic `Site`.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos188.UpperBound

/-- A site on the wire: two axial center fractions and a radius fraction as integers. -/
structure SiteWire where
  sNum : ℤ
  sDen : ℤ
  tNum : ℤ
  tDen : ℤ
  rNum : ℤ
  rDen : ℤ

/-- The semantic site of a wire site; the six integers are divided as rationals. -/
def SiteWire.toSite (site : SiteWire) : Site where
  center := ((site.sNum : ℚ) / site.sDen, (site.tNum : ℚ) / site.tDen)
  radius := (site.rNum : ℚ) / site.rDen

end Erdos188.UpperBound
