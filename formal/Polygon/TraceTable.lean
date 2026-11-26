import Polygon.Trace

/-! Exact traces for interval widths 1 to 29. Each identity is independently kernel-reduced. -/
namespace Polygon.Cert
set_option maxRecDepth 30000
set_option maxHeartbeats 1500000

def traceValue (d : ℕ) : ℕ :=
  [1,
   271443,
   1385407029,
   874569107071,
   154424192534978,
   11590981980134136,
   471109005712845073,
   12073893516637797647,
   216054227528911051598,
   2899588931289770319928,
   30747252105854418602807,
   267900870986039891665533,
   1976658261038065237688965,
   12646583259151935165028659,
   71505544338055517905383002,
   362852466483982941465664294,
   1673644967862052696066138463,
   7091534775916075003484209649,
   27850704697432295249191815709,
   102151810477267331847970867095,
   352204279293140920190902505756,
   1147947037059968833062938517298,
   3554264799119307289506871036659,
   10498698066409011044245276217901,
   29697044023575712453995735900724,
   80710316446302004065351530568318,
   211382155607852560741336416052863,
   534907644994676627454203692327477,
   1310960487246736777485104974336647].getD d 0

private theorem checked1 : traceCount 13 1 = 1 := by decide +kernel
private theorem checked2 : traceCount 13 2 = 271443 := by decide +kernel
private theorem checked3 : traceCount 13 3 = 1385407029 := by decide +kernel
private theorem checked4 : traceCount 13 4 = 874569107071 := by decide +kernel
private theorem checked5 : traceCount 13 5 = 154424192534978 := by decide +kernel
private theorem checked6 : traceCount 13 6 = 11590981980134136 := by decide +kernel
private theorem checked7 : traceCount 13 7 = 471109005712845073 := by decide +kernel
private theorem checked8 : traceCount 13 8 = 12073893516637797647 := by decide +kernel
private theorem checked9 : traceCount 13 9 = 216054227528911051598 := by decide +kernel
private theorem checked10 : traceCount 13 10 = 2899588931289770319928 := by decide +kernel
private theorem checked11 : traceCount 13 11 = 30747252105854418602807 := by decide +kernel
private theorem checked12 : traceCount 13 12 = 267900870986039891665533 := by decide +kernel
private theorem checked13 : traceCount 13 13 = 1976658261038065237688965 := by decide +kernel
private theorem checked14 : traceCount 13 14 = 12646583259151935165028659 := by decide +kernel
private theorem checked15 : traceCount 13 15 = 71505544338055517905383002 := by decide +kernel
private theorem checked16 : traceCount 13 16 = 362852466483982941465664294 := by decide +kernel
private theorem checked17 : traceCount 13 17 = 1673644967862052696066138463 := by decide +kernel
private theorem checked18 : traceCount 13 18 = 7091534775916075003484209649 := by decide +kernel
private theorem checked19 : traceCount 13 19 = 27850704697432295249191815709 := by decide +kernel
private theorem checked20 : traceCount 13 20 = 102151810477267331847970867095 := by decide +kernel
private theorem checked21 : traceCount 13 21 = 352204279293140920190902505756 := by decide +kernel
private theorem checked22 : traceCount 13 22 = 1147947037059968833062938517298 := by decide +kernel
private theorem checked23 : traceCount 13 23 = 3554264799119307289506871036659 := by decide +kernel
private theorem checked24 : traceCount 13 24 = 10498698066409011044245276217901 := by decide +kernel
private theorem checked25 : traceCount 13 25 = 29697044023575712453995735900724 := by decide +kernel
private theorem checked26 : traceCount 13 26 = 80710316446302004065351530568318 := by decide +kernel
private theorem checked27 : traceCount 13 27 = 211382155607852560741336416052863 := by decide +kernel
private theorem checked28 : traceCount 13 28 = 534907644994676627454203692327477 := by decide +kernel
private theorem checked29 : traceCount 13 29 = 1310960487246736777485104974336647 := by decide +kernel

theorem checked_trace (d : Fin 29) : traceCount 13 (d.val+1) = traceValue d.val := by
  fin_cases d
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27
  · exact checked28
  · exact checked29

#print axioms checked_trace
end Polygon.Cert
