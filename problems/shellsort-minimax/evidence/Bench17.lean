import Certificates
open ShellMinimax ShellMinimax.Certificate
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace ShellMinimax.Reflected17
run_cmd Lean.logInfo m!"begin_ms {← IO.monoMsNow}"
def p4 : List (Fin 17) := [7, 3, 16, 13, 10, 6, 2, 15, 12, 9, 5, 1, 14, 11, 8, 4, 0]
def p25 : List (Fin 17) := [2, 16, 8, 14, 6, 12, 4, 10, 1, 15, 7, 13, 5, 11, 3, 9, 0]
def p68 : List (Fin 17) := [8, 15, 4, 10, 14, 3, 9, 12, 16, 5, 2, 11, 0, 7, 13, 1, 6]
def p69 : List (Fin 17) := [8, 15, 4, 11, 7, 14, 3, 16, 5, 12, 2, 10, 0, 9, 6, 13, 1]
def p70 : List (Fin 17) := [14, 15, 5, 8, 12, 13, 4, 16, 6, 9, 0, 7, 2, 1, 10, 11, 3]
def p5 : List (Fin 17) := [13, 3, 10, 16, 8, 12, 2, 9, 15, 7, 11, 1, 6, 14, 5, 4, 0]
def p6 : List (Fin 17) := [13, 8, 14, 9, 16, 10, 5, 11, 6, 15, 2, 4, 7, 1, 12, 0, 3]
def p7 : List (Fin 17) := [6, 10, 11, 14, 16, 5, 9, 1, 12, 15, 4, 8, 0, 2, 13, 3, 7]
def p71 : List (Fin 17) := [2, 14, 6, 15, 7, 11, 3, 16, 8, 12, 0, 13, 5, 10, 4, 9, 1]
def p3 : List (Fin 17) := [7, 9, 14, 16, 6, 8, 11, 15, 3, 5, 10, 13, 2, 4, 1, 12, 0]
def p72 : List (Fin 17) := [14, 10, 12, 15, 4, 6, 11, 16, 5, 7, 13, 9, 3, 2, 0, 1, 8]
def p73 : List (Fin 17) := [14, 9, 4, 11, 15, 7, 2, 16, 8, 3, 13, 6, 0, 10, 12, 5, 1]
def p74 : List (Fin 17) := [10, 16, 8, 15, 6, 13, 4, 7, 14, 5, 0, 12, 3, 11, 2, 9, 1]
def p75 : List (Fin 17) := [12, 16, 4, 11, 14, 3, 7, 15, 5, 10, 8, 2, 0, 9, 13, 1, 6]
def p76 : List (Fin 17) := [16, 11, 6, 4, 14, 10, 5, 15, 12, 8, 7, 3, 0, 2, 13, 9, 1]
def p77 : List (Fin 17) := [13, 1, 14, 8, 15, 10, 5, 16, 11, 6, 12, 0, 4, 7, 2, 9, 3]
def p78 : List (Fin 17) := [2, 6, 11, 14, 4, 15, 9, 8, 16, 12, 0, 5, 3, 10, 1, 13, 7]
def p79 : List (Fin 17) := [8, 16, 4, 13, 14, 11, 6, 15, 12, 7, 0, 10, 3, 9, 5, 2, 1]
def p80 : List (Fin 17) := [3, 6, 16, 13, 14, 11, 9, 15, 12, 10, 0, 5, 8, 4, 2, 1, 7]
def p81 : List (Fin 17) := [3, 13, 15, 5, 7, 11, 4, 14, 8, 16, 0, 12, 10, 2, 6, 9, 1]
def p82 : List (Fin 17) := [14, 5, 16, 10, 3, 12, 8, 13, 9, 4, 7, 0, 15, 6, 2, 11, 1]
def p83 : List (Fin 17) := [13, 1, 11, 16, 9, 15, 5, 12, 6, 10, 4, 0, 8, 2, 7, 14, 3]
def p84 : List (Fin 17) := [10, 2, 16, 12, 5, 14, 8, 15, 9, 3, 7, 0, 4, 11, 1, 13, 6]
def p85 : List (Fin 17) := [10, 12, 9, 7, 4, 13, 14, 1, 15, 16, 0, 11, 8, 6, 3, 5, 2]
def p86 : List (Fin 17) := [3, 16, 12, 7, 15, 11, 4, 13, 5, 8, 0, 6, 10, 2, 14, 9, 1]
def p87 : List (Fin 17) := [15, 12, 8, 16, 14, 10, 6, 11, 7, 3, 5, 2, 0, 13, 9, 4, 1]
def p88 : List (Fin 17) := [12, 3, 16, 15, 10, 14, 8, 11, 9, 6, 7, 0, 5, 4, 2, 13, 1]
def p42 : List (Fin 17) := [15, 13, 11, 9, 7, 5, 3, 1, 16, 14, 12, 10, 8, 6, 4, 2, 0]
def p89 : List (Fin 17) := [14, 8, 12, 6, 11, 1, 3, 10, 15, 16, 13, 4, 9, 5, 7, 0, 2]
def p90 : List (Fin 17) := [8, 15, 12, 6, 14, 10, 4, 1, 16, 13, 7, 0, 11, 5, 2, 9, 3]
def p91 : List (Fin 17) := [14, 12, 6, 15, 13, 10, 5, 1, 7, 16, 4, 11, 2, 0, 8, 9, 3]
def p92 : List (Fin 17) := [16, 8, 11, 1, 15, 7, 9, 10, 12, 14, 13, 4, 2, 0, 5, 6, 3]
def p93 : List (Fin 17) := [9, 5, 13, 15, 11, 7, 3, 1, 16, 12, 8, 4, 0, 14, 10, 6, 2]
def p94 : List (Fin 17) := [6, 14, 13, 8, 15, 10, 4, 1, 16, 11, 5, 0, 12, 7, 2, 9, 3]
def p95 : List (Fin 17) := [13, 3, 14, 10, 15, 6, 12, 5, 16, 9, 8, 0, 4, 2, 11, 1, 7]
def p96 : List (Fin 17) := [9, 11, 16, 13, 14, 1, 7, 8, 15, 6, 5, 10, 12, 3, 2, 0, 4]
def p97 : List (Fin 17) := [11, 14, 2, 9, 13, 15, 5, 6, 16, 8, 7, 12, 0, 3, 10, 1, 4]
def p98 : List (Fin 17) := [15, 11, 2, 16, 14, 10, 4, 6, 12, 8, 3, 5, 0, 7, 13, 9, 1]
def p99 : List (Fin 17) := [13, 10, 16, 15, 3, 11, 7, 4, 12, 8, 0, 9, 5, 14, 2, 1, 6]
def p100 : List (Fin 17) := [11, 16, 5, 15, 14, 8, 1, 6, 9, 12, 10, 7, 4, 3, 13, 2, 0]
def p101 : List (Fin 17) := [13, 3, 15, 12, 4, 14, 10, 1, 11, 16, 9, 0, 7, 8, 2, 5, 6]
def p102 : List (Fin 17) := [9, 14, 13, 12, 5, 15, 6, 7, 8, 16, 0, 10, 4, 11, 3, 2, 1]
theorem mask256 : check (n := 17) 86 [10, 1] (.witness p4) = true := by decide
theorem mask257 : check (n := 17) 86 [10, 2, 1] (.witness p25) = true := by decide
theorem mask258 : check (n := 17) 86 [10, 3, 1] (.witness p68) = true := by decide
theorem mask259 : check (n := 17) 86 [10, 3, 2, 1] (.witness p68) = true := by decide
theorem mask260 : check (n := 17) 86 [10, 4, 1] (.witness p69) = true := by decide
theorem mask261 : check (n := 17) 86 [10, 4, 2, 1] (.witness p69) = true := by decide
theorem mask262 : check (n := 17) 86 [10, 4, 3, 1] (.witness p70) = true := by decide
theorem mask263 : check (n := 17) 86 [10, 4, 3, 2, 1] (.witness p70) = true := by decide
theorem mask264 : check (n := 17) 86 [10, 5, 1] (.witness p4) = true := by decide
theorem mask265 : check (n := 17) 86 [10, 5, 2, 1] (.witness p5) = true := by decide
theorem mask266 : check (n := 17) 86 [10, 5, 3, 1] (.witness p6) = true := by decide
theorem mask267 : check (n := 17) 86 [10, 5, 3, 2, 1] (.witness p6) = true := by decide
theorem mask268 : check (n := 17) 86 [10, 5, 4, 1] (.witness p7) = true := by decide
theorem mask269 : check (n := 17) 86 [10, 5, 4, 2, 1] (.witness p7) = true := by decide
theorem mask270 : check (n := 17) 86 [10, 5, 4, 3, 1] (.witness p70) = true := by decide
theorem mask271 : check (n := 17) 86 [10, 5, 4, 3, 2, 1] (.witness p70) = true := by decide
theorem mask272 : check (n := 17) 86 [10, 6, 1] (.witness p71) = true := by decide
theorem mask273 : check (n := 17) 86 [10, 6, 2, 1] (.witness p71) = true := by decide
theorem mask274 : check (n := 17) 86 [10, 6, 3, 1] (.witness p68) = true := by decide
theorem mask275 : check (n := 17) 86 [10, 6, 3, 2, 1] (.witness p68) = true := by decide
theorem mask276 : check (n := 17) 86 [10, 6, 4, 1] (.witness p69) = true := by decide
theorem mask277 : check (n := 17) 86 [10, 6, 4, 2, 1] (.witness p69) = true := by decide
theorem mask278 : check (n := 17) 86 [10, 6, 4, 3, 1] (.witness p71) = true := by decide
theorem mask279 : check (n := 17) 86 [10, 6, 4, 3, 2, 1] (.witness p71) = true := by decide
theorem mask280 : check (n := 17) 86 [10, 6, 5, 1] (.witness p4) = true := by decide
theorem mask281 : check (n := 17) 86 [10, 6, 5, 2, 1] (.witness p3) = true := by decide
theorem mask282 : check (n := 17) 86 [10, 6, 5, 3, 1] (.witness p68) = true := by decide
theorem mask283 : check (n := 17) 86 [10, 6, 5, 3, 2, 1] (.witness p68) = true := by decide
theorem mask284 : check (n := 17) 86 [10, 6, 5, 4, 1] (.witness p72) = true := by decide
theorem mask285 : check (n := 17) 86 [10, 6, 5, 4, 2, 1] (.witness p72) = true := by decide
theorem mask286 : check (n := 17) 86 [10, 6, 5, 4, 3, 1] (.witness p72) = true := by decide
theorem mask287 : check (n := 17) 86 [10, 6, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask288 : check (n := 17) 86 [10, 7, 1] (.witness p73) = true := by decide
theorem mask289 : check (n := 17) 86 [10, 7, 2, 1] (.witness p74) = true := by decide
theorem mask290 : check (n := 17) 86 [10, 7, 3, 1] (.witness p75) = true := by decide
theorem mask291 : check (n := 17) 86 [10, 7, 3, 2, 1] (.witness p75) = true := by decide
theorem mask292 : check (n := 17) 86 [10, 7, 4, 1] (.witness p76) = true := by decide
theorem mask293 : check (n := 17) 86 [10, 7, 4, 2, 1] (.witness p76) = true := by decide
theorem mask294 : check (n := 17) 86 [10, 7, 4, 3, 1] (.witness p76) = true := by decide
theorem mask295 : check (n := 17) 86 [10, 7, 4, 3, 2, 1] (.witness p76) = true := by decide
theorem mask296 : check (n := 17) 86 [10, 7, 5, 1] (.witness p77) = true := by decide
theorem mask297 : check (n := 17) 86 [10, 7, 5, 2, 1] (.witness p77) = true := by decide
theorem mask298 : check (n := 17) 86 [10, 7, 5, 3, 1] (.witness p77) = true := by decide
theorem mask299 : check (n := 17) 86 [10, 7, 5, 3, 2, 1] (.witness p77) = true := by decide
theorem mask300 : check (n := 17) 86 [10, 7, 5, 4, 1] (.witness p78) = true := by decide
theorem mask301 : check (n := 17) 86 [10, 7, 5, 4, 2, 1] (.witness p78) = true := by decide
theorem mask302 : check (n := 17) 86 [10, 7, 5, 4, 3, 1] (.witness p78) = true := by decide
theorem mask303 : check (n := 17) 86 [10, 7, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask304 : check (n := 17) 86 [10, 7, 6, 1] (.witness p79) = true := by decide
theorem mask305 : check (n := 17) 86 [10, 7, 6, 2, 1] (.witness p79) = true := by decide
theorem mask306 : check (n := 17) 86 [10, 7, 6, 3, 1] (.witness p79) = true := by decide
theorem mask307 : check (n := 17) 86 [10, 7, 6, 3, 2, 1] (.witness p79) = true := by decide
theorem mask308 : check (n := 17) 86 [10, 7, 6, 4, 1] (.witness p79) = true := by decide
theorem mask309 : check (n := 17) 86 [10, 7, 6, 4, 2, 1] (.witness p79) = true := by decide
theorem mask310 : check (n := 17) 86 [10, 7, 6, 4, 3, 1] (.witness p79) = true := by decide
theorem mask311 : check (n := 17) 86 [10, 7, 6, 4, 3, 2, 1] (.witness p79) = true := by decide
theorem mask312 : check (n := 17) 86 [10, 7, 6, 5, 1] (.witness p80) = true := by decide
theorem mask313 : check (n := 17) 86 [10, 7, 6, 5, 2, 1] (.witness p80) = true := by decide
theorem mask314 : check (n := 17) 86 [10, 7, 6, 5, 3, 1] (.witness p80) = true := by decide
theorem mask315 : check (n := 17) 86 [10, 7, 6, 5, 3, 2, 1] (.witness p80) = true := by decide
theorem mask316 : check (n := 17) 86 [10, 7, 6, 5, 4, 1] (.witness p80) = true := by decide
theorem mask317 : check (n := 17) 86 [10, 7, 6, 5, 4, 2, 1] (.witness p80) = true := by decide
theorem mask318 : check (n := 17) 86 [10, 7, 6, 5, 4, 3, 1] (.witness p80) = true := by decide
theorem mask319 : check (n := 17) 86 [10, 7, 6, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask320 : check (n := 17) 86 [10, 8, 1] (.witness p25) = true := by decide
theorem mask321 : check (n := 17) 86 [10, 8, 2, 1] (.witness p25) = true := by decide
theorem mask322 : check (n := 17) 86 [10, 8, 3, 1] (.witness p81) = true := by decide
theorem mask323 : check (n := 17) 86 [10, 8, 3, 2, 1] (.witness p81) = true := by decide
theorem mask324 : check (n := 17) 86 [10, 8, 4, 1] (.witness p25) = true := by decide
theorem mask325 : check (n := 17) 86 [10, 8, 4, 2, 1] (.witness p25) = true := by decide
theorem mask326 : check (n := 17) 86 [10, 8, 4, 3, 1] (.witness p25) = true := by decide
theorem mask327 : check (n := 17) 86 [10, 8, 4, 3, 2, 1] (.witness p25) = true := by decide
theorem mask328 : check (n := 17) 86 [10, 8, 5, 1] (.witness p82) = true := by decide
theorem mask329 : check (n := 17) 86 [10, 8, 5, 2, 1] (.witness p83) = true := by decide
theorem mask330 : check (n := 17) 86 [10, 8, 5, 3, 1] (.witness p82) = true := by decide
theorem mask331 : check (n := 17) 86 [10, 8, 5, 3, 2, 1] (.witness p82) = true := by decide
theorem mask332 : check (n := 17) 86 [10, 8, 5, 4, 1] (.witness p83) = true := by decide
theorem mask333 : check (n := 17) 86 [10, 8, 5, 4, 2, 1] (.witness p83) = true := by decide
theorem mask334 : check (n := 17) 86 [10, 8, 5, 4, 3, 1] (.witness p83) = true := by decide
theorem mask335 : check (n := 17) 86 [10, 8, 5, 4, 3, 2, 1] (.witness p83) = true := by decide
theorem mask336 : check (n := 17) 86 [10, 8, 6, 1] (.witness p25) = true := by decide
theorem mask337 : check (n := 17) 86 [10, 8, 6, 2, 1] (.witness p25) = true := by decide
theorem mask338 : check (n := 17) 86 [10, 8, 6, 3, 1] (.witness p81) = true := by decide
theorem mask339 : check (n := 17) 86 [10, 8, 6, 3, 2, 1] (.witness p81) = true := by decide
theorem mask340 : check (n := 17) 86 [10, 8, 6, 4, 1] (.witness p25) = true := by decide
theorem mask341 : check (n := 17) 86 [10, 8, 6, 4, 2, 1] (.witness p25) = true := by decide
theorem mask342 : check (n := 17) 86 [10, 8, 6, 4, 3, 1] (.witness p25) = true := by decide
theorem mask343 : check (n := 17) 86 [10, 8, 6, 4, 3, 2, 1] (.witness p25) = true := by decide
theorem mask344 : check (n := 17) 86 [10, 8, 6, 5, 1] (.witness p84) = true := by decide
theorem mask345 : check (n := 17) 86 [10, 8, 6, 5, 2, 1] (.witness p84) = true := by decide
theorem mask346 : check (n := 17) 86 [10, 8, 6, 5, 3, 1] (.witness p84) = true := by decide
theorem mask347 : check (n := 17) 86 [10, 8, 6, 5, 3, 2, 1] (.witness p84) = true := by decide
theorem mask348 : check (n := 17) 86 [10, 8, 6, 5, 4, 1] (.witness p84) = true := by decide
theorem mask349 : check (n := 17) 86 [10, 8, 6, 5, 4, 2, 1] (.witness p84) = true := by decide
theorem mask350 : check (n := 17) 86 [10, 8, 6, 5, 4, 3, 1] (.witness p84) = true := by decide
theorem mask351 : check (n := 17) 86 [10, 8, 6, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask352 : check (n := 17) 86 [10, 8, 7, 1] (.witness p85) = true := by decide
theorem mask353 : check (n := 17) 86 [10, 8, 7, 2, 1] (.witness p74) = true := by decide
theorem mask354 : check (n := 17) 86 [10, 8, 7, 3, 1] (.witness p86) = true := by decide
theorem mask355 : check (n := 17) 86 [10, 8, 7, 3, 2, 1] (.witness p86) = true := by decide
theorem mask356 : check (n := 17) 86 [10, 8, 7, 4, 1] (.witness p87) = true := by decide
theorem mask357 : check (n := 17) 86 [10, 8, 7, 4, 2, 1] (.witness p87) = true := by decide
theorem mask358 : check (n := 17) 86 [10, 8, 7, 4, 3, 1] (.witness p87) = true := by decide
theorem mask359 : check (n := 17) 86 [10, 8, 7, 4, 3, 2, 1] (.witness p87) = true := by decide
theorem mask360 : check (n := 17) 86 [10, 8, 7, 5, 1] (.witness p88) = true := by decide
theorem mask361 : check (n := 17) 86 [10, 8, 7, 5, 2, 1] (.witness p88) = true := by decide
theorem mask362 : check (n := 17) 86 [10, 8, 7, 5, 3, 1] (.witness p88) = true := by decide
theorem mask363 : check (n := 17) 86 [10, 8, 7, 5, 3, 2, 1] (.witness p88) = true := by decide
theorem mask364 : check (n := 17) 86 [10, 8, 7, 5, 4, 1] (.witness p88) = true := by decide
theorem mask365 : check (n := 17) 86 [10, 8, 7, 5, 4, 2, 1] (.witness p88) = true := by decide
theorem mask366 : check (n := 17) 86 [10, 8, 7, 5, 4, 3, 1] (.witness p88) = true := by decide
theorem mask367 : check (n := 17) 86 [10, 8, 7, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask368 : check (n := 17) 86 [10, 8, 7, 6, 1] (.witness p74) = true := by decide
theorem mask369 : check (n := 17) 86 [10, 8, 7, 6, 2, 1] (.witness p74) = true := by decide
theorem mask370 : check (n := 17) 86 [10, 8, 7, 6, 3, 1] (.witness p86) = true := by decide
theorem mask371 : check (n := 17) 86 [10, 8, 7, 6, 3, 2, 1] (.witness p86) = true := by decide
theorem mask372 : check (n := 17) 86 [10, 8, 7, 6, 4, 1] (.witness p86) = true := by decide
theorem mask373 : check (n := 17) 86 [10, 8, 7, 6, 4, 2, 1] (.witness p86) = true := by decide
theorem mask374 : check (n := 17) 86 [10, 8, 7, 6, 4, 3, 1] (.witness p86) = true := by decide
theorem mask375 : check (n := 17) 86 [10, 8, 7, 6, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask376 : check (n := 17) 86 [10, 8, 7, 6, 5, 1] (.witness p88) = true := by decide
theorem mask377 : check (n := 17) 86 [10, 8, 7, 6, 5, 2, 1] (.witness p88) = true := by decide
theorem mask378 : check (n := 17) 86 [10, 8, 7, 6, 5, 3, 1] (.witness p88) = true := by decide
theorem mask379 : check (n := 17) 86 [10, 8, 7, 6, 5, 3, 2, 1] (.baseline) = true := by decide
theorem mask380 : check (n := 17) 86 [10, 8, 7, 6, 5, 4, 1] (.witness p88) = true := by decide
theorem mask381 : check (n := 17) 86 [10, 8, 7, 6, 5, 4, 2, 1] (.baseline) = true := by decide
theorem mask382 : check (n := 17) 86 [10, 8, 7, 6, 5, 4, 3, 1] (.baseline) = true := by decide
theorem mask383 : check (n := 17) 86 [10, 8, 7, 6, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask384 : check (n := 17) 86 [10, 9, 1] (.witness p42) = true := by decide
theorem mask385 : check (n := 17) 86 [10, 9, 2, 1] (.witness p89) = true := by decide
theorem mask386 : check (n := 17) 86 [10, 9, 3, 1] (.witness p90) = true := by decide
theorem mask387 : check (n := 17) 86 [10, 9, 3, 2, 1] (.witness p90) = true := by decide
theorem mask388 : check (n := 17) 86 [10, 9, 4, 1] (.witness p91) = true := by decide
theorem mask389 : check (n := 17) 86 [10, 9, 4, 2, 1] (.witness p91) = true := by decide
theorem mask390 : check (n := 17) 86 [10, 9, 4, 3, 1] (.witness p92) = true := by decide
theorem mask391 : check (n := 17) 86 [10, 9, 4, 3, 2, 1] (.witness p92) = true := by decide
theorem mask392 : check (n := 17) 86 [10, 9, 5, 1] (.witness p93) = true := by decide
theorem mask393 : check (n := 17) 86 [10, 9, 5, 2, 1] (.witness p93) = true := by decide
theorem mask394 : check (n := 17) 86 [10, 9, 5, 3, 1] (.witness p93) = true := by decide
theorem mask395 : check (n := 17) 86 [10, 9, 5, 3, 2, 1] (.witness p93) = true := by decide
theorem mask396 : check (n := 17) 86 [10, 9, 5, 4, 1] (.witness p7) = true := by decide
theorem mask397 : check (n := 17) 86 [10, 9, 5, 4, 2, 1] (.witness p7) = true := by decide
theorem mask398 : check (n := 17) 86 [10, 9, 5, 4, 3, 1] (.witness p7) = true := by decide
theorem mask399 : check (n := 17) 86 [10, 9, 5, 4, 3, 2, 1] (.witness p7) = true := by decide
theorem mask400 : check (n := 17) 86 [10, 9, 6, 1] (.witness p94) = true := by decide
theorem mask401 : check (n := 17) 86 [10, 9, 6, 2, 1] (.witness p89) = true := by decide
theorem mask402 : check (n := 17) 86 [10, 9, 6, 3, 1] (.witness p90) = true := by decide
theorem mask403 : check (n := 17) 86 [10, 9, 6, 3, 2, 1] (.witness p90) = true := by decide
theorem mask404 : check (n := 17) 86 [10, 9, 6, 4, 1] (.witness p95) = true := by decide
theorem mask405 : check (n := 17) 86 [10, 9, 6, 4, 2, 1] (.witness p95) = true := by decide
theorem mask406 : check (n := 17) 86 [10, 9, 6, 4, 3, 1] (.witness p95) = true := by decide
theorem mask407 : check (n := 17) 86 [10, 9, 6, 4, 3, 2, 1] (.witness p95) = true := by decide
theorem mask408 : check (n := 17) 86 [10, 9, 6, 5, 1] (.witness p96) = true := by decide
theorem mask409 : check (n := 17) 86 [10, 9, 6, 5, 2, 1] (.witness p96) = true := by decide
theorem mask410 : check (n := 17) 86 [10, 9, 6, 5, 3, 1] (.witness p96) = true := by decide
theorem mask411 : check (n := 17) 86 [10, 9, 6, 5, 3, 2, 1] (.witness p96) = true := by decide
theorem mask412 : check (n := 17) 86 [10, 9, 6, 5, 4, 1] (.witness p96) = true := by decide
theorem mask413 : check (n := 17) 86 [10, 9, 6, 5, 4, 2, 1] (.witness p96) = true := by decide
theorem mask414 : check (n := 17) 86 [10, 9, 6, 5, 4, 3, 1] (.witness p96) = true := by decide
theorem mask415 : check (n := 17) 86 [10, 9, 6, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask416 : check (n := 17) 86 [10, 9, 7, 1] (.witness p85) = true := by decide
theorem mask417 : check (n := 17) 86 [10, 9, 7, 2, 1] (.witness p74) = true := by decide
theorem mask418 : check (n := 17) 86 [10, 9, 7, 3, 1] (.witness p97) = true := by decide
theorem mask419 : check (n := 17) 86 [10, 9, 7, 3, 2, 1] (.witness p97) = true := by decide
theorem mask420 : check (n := 17) 86 [10, 9, 7, 4, 1] (.witness p98) = true := by decide
theorem mask421 : check (n := 17) 86 [10, 9, 7, 4, 2, 1] (.witness p98) = true := by decide
theorem mask422 : check (n := 17) 86 [10, 9, 7, 4, 3, 1] (.witness p98) = true := by decide
theorem mask423 : check (n := 17) 86 [10, 9, 7, 4, 3, 2, 1] (.witness p98) = true := by decide
theorem mask424 : check (n := 17) 86 [10, 9, 7, 5, 1] (.witness p99) = true := by decide
theorem mask425 : check (n := 17) 86 [10, 9, 7, 5, 2, 1] (.witness p99) = true := by decide
theorem mask426 : check (n := 17) 86 [10, 9, 7, 5, 3, 1] (.witness p99) = true := by decide
theorem mask427 : check (n := 17) 86 [10, 9, 7, 5, 3, 2, 1] (.witness p99) = true := by decide
theorem mask428 : check (n := 17) 86 [10, 9, 7, 5, 4, 1] (.witness p99) = true := by decide
theorem mask429 : check (n := 17) 86 [10, 9, 7, 5, 4, 2, 1] (.witness p99) = true := by decide
theorem mask430 : check (n := 17) 86 [10, 9, 7, 5, 4, 3, 1] (.witness p99) = true := by decide
theorem mask431 : check (n := 17) 86 [10, 9, 7, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask432 : check (n := 17) 86 [10, 9, 7, 6, 1] (.witness p100) = true := by decide
theorem mask433 : check (n := 17) 86 [10, 9, 7, 6, 2, 1] (.witness p100) = true := by decide
theorem mask434 : check (n := 17) 86 [10, 9, 7, 6, 3, 1] (.witness p100) = true := by decide
theorem mask435 : check (n := 17) 86 [10, 9, 7, 6, 3, 2, 1] (.witness p100) = true := by decide
theorem mask436 : check (n := 17) 86 [10, 9, 7, 6, 4, 1] (.witness p99) = true := by decide
theorem mask437 : check (n := 17) 86 [10, 9, 7, 6, 4, 2, 1] (.witness p99) = true := by decide
theorem mask438 : check (n := 17) 86 [10, 9, 7, 6, 4, 3, 1] (.witness p99) = true := by decide
theorem mask439 : check (n := 17) 86 [10, 9, 7, 6, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask440 : check (n := 17) 86 [10, 9, 7, 6, 5, 1] (.witness p99) = true := by decide
theorem mask441 : check (n := 17) 86 [10, 9, 7, 6, 5, 2, 1] (.witness p99) = true := by decide
theorem mask442 : check (n := 17) 86 [10, 9, 7, 6, 5, 3, 1] (.witness p99) = true := by decide
theorem mask443 : check (n := 17) 86 [10, 9, 7, 6, 5, 3, 2, 1] (.baseline) = true := by decide
theorem mask444 : check (n := 17) 86 [10, 9, 7, 6, 5, 4, 1] (.witness p99) = true := by decide
theorem mask445 : check (n := 17) 86 [10, 9, 7, 6, 5, 4, 2, 1] (.baseline) = true := by decide
theorem mask446 : check (n := 17) 86 [10, 9, 7, 6, 5, 4, 3, 1] (.baseline) = true := by decide
theorem mask447 : check (n := 17) 86 [10, 9, 7, 6, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask448 : check (n := 17) 86 [10, 9, 8, 1] (.witness p89) = true := by decide
theorem mask449 : check (n := 17) 86 [10, 9, 8, 2, 1] (.witness p89) = true := by decide
theorem mask450 : check (n := 17) 86 [10, 9, 8, 3, 1] (.witness p101) = true := by decide
theorem mask451 : check (n := 17) 86 [10, 9, 8, 3, 2, 1] (.witness p101) = true := by decide
theorem mask452 : check (n := 17) 86 [10, 9, 8, 4, 1] (.witness p91) = true := by decide
theorem mask453 : check (n := 17) 86 [10, 9, 8, 4, 2, 1] (.witness p91) = true := by decide
theorem mask454 : check (n := 17) 86 [10, 9, 8, 4, 3, 1] (.witness p91) = true := by decide
theorem mask455 : check (n := 17) 86 [10, 9, 8, 4, 3, 2, 1] (.witness p91) = true := by decide
theorem mask456 : check (n := 17) 86 [10, 9, 8, 5, 1] (.witness p4) = true := by decide
theorem mask457 : check (n := 17) 86 [10, 9, 8, 5, 2, 1] (.witness p7) = true := by decide
theorem mask458 : check (n := 17) 86 [10, 9, 8, 5, 3, 1] (.witness p101) = true := by decide
theorem mask459 : check (n := 17) 86 [10, 9, 8, 5, 3, 2, 1] (.witness p101) = true := by decide
theorem mask460 : check (n := 17) 86 [10, 9, 8, 5, 4, 1] (.witness p95) = true := by decide
theorem mask461 : check (n := 17) 86 [10, 9, 8, 5, 4, 2, 1] (.witness p95) = true := by decide
theorem mask462 : check (n := 17) 86 [10, 9, 8, 5, 4, 3, 1] (.witness p95) = true := by decide
theorem mask463 : check (n := 17) 86 [10, 9, 8, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask464 : check (n := 17) 86 [10, 9, 8, 6, 1] (.witness p102) = true := by decide
theorem mask465 : check (n := 17) 86 [10, 9, 8, 6, 2, 1] (.witness p102) = true := by decide
theorem mask466 : check (n := 17) 86 [10, 9, 8, 6, 3, 1] (.witness p102) = true := by decide
theorem mask467 : check (n := 17) 86 [10, 9, 8, 6, 3, 2, 1] (.witness p102) = true := by decide
theorem mask468 : check (n := 17) 86 [10, 9, 8, 6, 4, 1] (.witness p102) = true := by decide
theorem mask469 : check (n := 17) 86 [10, 9, 8, 6, 4, 2, 1] (.witness p102) = true := by decide
theorem mask470 : check (n := 17) 86 [10, 9, 8, 6, 4, 3, 1] (.witness p102) = true := by decide
theorem mask471 : check (n := 17) 86 [10, 9, 8, 6, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask472 : check (n := 17) 86 [10, 9, 8, 6, 5, 1] (.witness p99) = true := by decide
theorem mask473 : check (n := 17) 86 [10, 9, 8, 6, 5, 2, 1] (.witness p99) = true := by decide
theorem mask474 : check (n := 17) 86 [10, 9, 8, 6, 5, 3, 1] (.witness p99) = true := by decide
theorem mask475 : check (n := 17) 86 [10, 9, 8, 6, 5, 3, 2, 1] (.baseline) = true := by decide
theorem mask476 : check (n := 17) 86 [10, 9, 8, 6, 5, 4, 1] (.witness p99) = true := by decide
theorem mask477 : check (n := 17) 86 [10, 9, 8, 6, 5, 4, 2, 1] (.baseline) = true := by decide
theorem mask478 : check (n := 17) 86 [10, 9, 8, 6, 5, 4, 3, 1] (.baseline) = true := by decide
theorem mask479 : check (n := 17) 86 [10, 9, 8, 6, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask480 : check (n := 17) 86 [10, 9, 8, 7, 1] (.witness p42) = true := by decide
theorem mask481 : check (n := 17) 86 [10, 9, 8, 7, 2, 1] (.witness p42) = true := by decide
theorem mask482 : check (n := 17) 86 [10, 9, 8, 7, 3, 1] (.witness p100) = true := by decide
theorem mask483 : check (n := 17) 86 [10, 9, 8, 7, 3, 2, 1] (.witness p100) = true := by decide
theorem mask484 : check (n := 17) 86 [10, 9, 8, 7, 4, 1] (.witness p98) = true := by decide
theorem mask485 : check (n := 17) 86 [10, 9, 8, 7, 4, 2, 1] (.witness p98) = true := by decide
theorem mask486 : check (n := 17) 86 [10, 9, 8, 7, 4, 3, 1] (.witness p98) = true := by decide
theorem mask487 : check (n := 17) 86 [10, 9, 8, 7, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask488 : check (n := 17) 86 [10, 9, 8, 7, 5, 1] (.witness p89) = true := by decide
theorem mask489 : check (n := 17) 86 [10, 9, 8, 7, 5, 2, 1] (.witness p89) = true := by decide
theorem mask490 : check (n := 17) 86 [10, 9, 8, 7, 5, 3, 1] (.witness p89) = true := by decide
theorem mask491 : check (n := 17) 86 [10, 9, 8, 7, 5, 3, 2, 1] (.baseline) = true := by decide
theorem mask492 : check (n := 17) 86 [10, 9, 8, 7, 5, 4, 1] (.witness p89) = true := by decide
theorem mask493 : check (n := 17) 86 [10, 9, 8, 7, 5, 4, 2, 1] (.baseline) = true := by decide
theorem mask494 : check (n := 17) 86 [10, 9, 8, 7, 5, 4, 3, 1] (.baseline) = true := by decide
theorem mask495 : check (n := 17) 86 [10, 9, 8, 7, 5, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask496 : check (n := 17) 86 [10, 9, 8, 7, 6, 1] (.witness p42) = true := by decide
theorem mask497 : check (n := 17) 86 [10, 9, 8, 7, 6, 2, 1] (.witness p42) = true := by decide
theorem mask498 : check (n := 17) 86 [10, 9, 8, 7, 6, 3, 1] (.witness p42) = true := by decide
theorem mask499 : check (n := 17) 86 [10, 9, 8, 7, 6, 3, 2, 1] (.baseline) = true := by decide
theorem mask500 : check (n := 17) 86 [10, 9, 8, 7, 6, 4, 1] (.witness p42) = true := by decide
theorem mask501 : check (n := 17) 86 [10, 9, 8, 7, 6, 4, 2, 1] (.baseline) = true := by decide
theorem mask502 : check (n := 17) 86 [10, 9, 8, 7, 6, 4, 3, 1] (.baseline) = true := by decide
theorem mask503 : check (n := 17) 86 [10, 9, 8, 7, 6, 4, 3, 2, 1] (.baseline) = true := by decide
theorem mask504 : check (n := 17) 86 [10, 9, 8, 7, 6, 5, 1] (.witness p42) = true := by decide
theorem mask505 : check (n := 17) 86 [10, 9, 8, 7, 6, 5, 2, 1] (.baseline) = true := by decide
theorem mask506 : check (n := 17) 86 [10, 9, 8, 7, 6, 5, 3, 1] (.baseline) = true := by decide
theorem mask507 : check (n := 17) 86 [10, 9, 8, 7, 6, 5, 3, 2, 1] (.baseline) = true := by decide
theorem mask508 : check (n := 17) 86 [10, 9, 8, 7, 6, 5, 4, 1] (.witness p42) = true := by decide
theorem mask509 : check (n := 17) 86 [10, 9, 8, 7, 6, 5, 4, 2, 1] (.baseline) = true := by decide
theorem mask510 : check (n := 17) 86 [10, 9, 8, 7, 6, 5, 4, 3, 1] (.baseline) = true := by decide
theorem mask511 : check (n := 17) 86 [10, 9, 8, 7, 6, 5, 4, 3, 2, 1] (.baseline) = true := by decide
run_cmd Lean.logInfo m!"end_ms {← IO.monoMsNow}"
end ShellMinimax.Reflected17
