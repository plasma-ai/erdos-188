module

public import Erdos188.LowerBound.Certificate.Checker

/-!
# Kernel evaluation of the certificate, intervals 31–40

Each interval check is proved by kernel evaluation (`decide +kernel`). The
intervals are split over several modules so that they are checked in parallel.
-/

@[expose] public section

namespace Erdos188.LowerBound.Certificate

theorem checkInterval_31 : checkInterval 31 = true := by decide +kernel

theorem checkInterval_32 : checkInterval 32 = true := by decide +kernel

theorem checkInterval_33 : checkInterval 33 = true := by decide +kernel

theorem checkInterval_34 : checkInterval 34 = true := by decide +kernel

theorem checkInterval_35 : checkInterval 35 = true := by decide +kernel

theorem checkInterval_36 : checkInterval 36 = true := by decide +kernel

theorem checkInterval_37 : checkInterval 37 = true := by decide +kernel

theorem checkInterval_38 : checkInterval 38 = true := by decide +kernel

theorem checkInterval_39 : checkInterval 39 = true := by decide +kernel

theorem checkInterval_40 : checkInterval 40 = true := by decide +kernel

end Erdos188.LowerBound.Certificate
