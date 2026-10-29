module

public import Erdos188.LowerBound.Certificate.Checker

/-!
# Kernel evaluation of the certificate, intervals 11–20

Each interval check is proved by kernel evaluation (`decide +kernel`). The
intervals are split over several modules so that they are checked in parallel.
-/

@[expose] public section

namespace Erdos188.LowerBound.Certificate

theorem checkInterval_11 : checkInterval 11 = true := by decide +kernel

theorem checkInterval_12 : checkInterval 12 = true := by decide +kernel

theorem checkInterval_13 : checkInterval 13 = true := by decide +kernel

theorem checkInterval_14 : checkInterval 14 = true := by decide +kernel

theorem checkInterval_15 : checkInterval 15 = true := by decide +kernel

theorem checkInterval_16 : checkInterval 16 = true := by decide +kernel

theorem checkInterval_17 : checkInterval 17 = true := by decide +kernel

theorem checkInterval_18 : checkInterval 18 = true := by decide +kernel

theorem checkInterval_19 : checkInterval 19 = true := by decide +kernel

theorem checkInterval_20 : checkInterval 20 = true := by decide +kernel

end Erdos188.LowerBound.Certificate
