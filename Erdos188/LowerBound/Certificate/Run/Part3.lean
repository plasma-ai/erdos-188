module

public import Erdos188.LowerBound.Certificate.Checker

/-!
# Kernel evaluation of the certificate, intervals 21–30

Each interval check is proved by kernel evaluation (`decide +kernel`). The
intervals are split over several modules so that they are checked in parallel.
-/

@[expose] public section

namespace Erdos188.LowerBound.Certificate

theorem checkInterval_21 : checkInterval 21 = true := by decide +kernel

theorem checkInterval_22 : checkInterval 22 = true := by decide +kernel

theorem checkInterval_23 : checkInterval 23 = true := by decide +kernel

theorem checkInterval_24 : checkInterval 24 = true := by decide +kernel

theorem checkInterval_25 : checkInterval 25 = true := by decide +kernel

theorem checkInterval_26 : checkInterval 26 = true := by decide +kernel

theorem checkInterval_27 : checkInterval 27 = true := by decide +kernel

theorem checkInterval_28 : checkInterval 28 = true := by decide +kernel

theorem checkInterval_29 : checkInterval 29 = true := by decide +kernel

theorem checkInterval_30 : checkInterval 30 = true := by decide +kernel

end Erdos188.LowerBound.Certificate
