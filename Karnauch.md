# 3 variables 

1. (A + B + C) = 0 
2. (1-A)(1-B) = 1 
3. (1-A)(2 - B - C) = 1 
4. A = 1 
5. (2 - A + C)(2 - A + B) = 1 
6. AB = 0 
7. (A + B + C) = 3 

# 4 variables 

1. A + B + C + D = 0
2. A + B + C = 0 
3. A + B + CD = 1         
4. A + B = 0 
5. A + BC + BD= 0       
6. A + BC = 0 
7. A + BCD = 0 
8. A = 0 
9. A(B + C + D) = 0
10. A(B + C) = 0 
11. AB + ACD = 0     (needs 2 constraints !!)
12. AB = 0 
13. AB(C + D) = 0     (needs 2 constraints !!) 
14. ABC = 0 
14. ABCD = 0 

-----------

# Lemmas

```hs
if p then a else b <=> (1-p)b + pa 

if p then 1 else b <=> (1-p)b + p
if p then 0 else b <=> (1-p)b
if p then a else 1 <=> 1 - p + pa 
if p then a else 0 <=> pa 
```