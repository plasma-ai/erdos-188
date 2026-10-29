module

public import Erdos188.LowerBound.Certificate.Checker

/-!
# Kernel evaluation of the certificate, intervals 0–10

Each interval check is proved by kernel evaluation (`decide +kernel`). The
intervals are split over several modules so that they are checked in parallel.
-/

@[expose] public section

namespace Erdos188.LowerBound.Certificate

theorem checkInterval_0 : checkInterval 0 = true := by decide +kernel

theorem checkInterval_1 : checkInterval 1 = true := by decide +kernel

theorem checkInterval_2 : checkInterval 2 = true := by decide +kernel

theorem checkInterval_3 : checkInterval 3 = true := by decide +kernel

theorem checkInterval_4 : checkInterval 4 = true := by decide +kernel

theorem checkInterval_5 : checkInterval 5 = true := by decide +kernel

theorem checkInterval_6 : checkInterval 6 = true := by decide +kernel

theorem checkInterval_7 : checkInterval 7 = true := by decide +kernel

theorem checkInterval_8 : checkInterval 8 = true := by decide +kernel

theorem checkInterval_9 : checkInterval 9 = true := by decide +kernel

theorem checkInterval_10 : checkInterval 10 = true := by decide +kernel

end Erdos188.LowerBound.Certificate
