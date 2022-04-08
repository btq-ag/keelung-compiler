# 2 variables (BA)
1. BA = 0
2. B = 0
3. B(1-A) = 1

# 3 variables (CBA)
1. C + B + A = 0 
2. (1-B)(1-A) = 1 
3. (1-C)(2 - B - A) = 1 
4. C = 1 
5. (2 - C + A)(2 - C + B) = 1 
6. CB = 0 
7. CBA = 0                      (needs 2 constraints !!)

# 4 variables (DCBA)

1. D + C + B + A = 0
2. D + C + B     = 0 
3. D + C + BA = 1         
4. D + C = 0 
5. D + CB + CA = 0
6. D + CB = 0 
7. D + CBA = 0 
8. D = 0 
9. D(C + B + A) = 0
10. D(C + B) = 0 
11. DC + DBA = 0     (needs 2 constraints !!)
12. CD = 0 
13. DC(B + A) = 0    (needs 2 constraints !!) 
14. DCB = 0          (needs 2 constraints !!) 
15. DCBA = 0         (needs 3 constraints !!) 

-----------

# Lemmas

```hs
if p then a else b <=> (1-p)b + pa 

if p then 1 else b <=> (1-p)b + p
if p then 0 else b <=> (1-p)b
if p then a else 1 <=> 1 - p + pa 
if p then a else 0 <=> pa 
```