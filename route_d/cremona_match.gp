/* Match psi1/psi2 trace pairs against Cremona curves with conductor supported on {2,3,5,11,13,97,163}. */
D = readvec("quot_11_3_65_2_1.txt");
pairs(a1, s2, p) = my(P = 'x^4 - a1*'x^3 + (a1^2 - s2)/2*'x^2 - p*a1*'x + p^2, f = factor(P)[, 1]); if(#f == 1 && poldegree(f[1]) == 2, [-polcoeff(f[1], 1)], apply(g -> -polcoeff(g, 1), f~));
S1 = vector(#D, i, pairs(D[i][3], D[i][4], D[i][1]));
S2 = vector(#D, i, pairs(D[i][5], D[i][6], D[i][1]));
Ns = List(); forstep(N = 2, 499999, 1, if(setminus(Set(factor(N)[, 1]~), [2,3,5,11,13,97,163]) == [], listput(Ns, N)));
print(#Ns, " conductors to scan");
{foreach(Ns, N, iferr(forell(e, N, N, my(E = ellinit(e[2]), m1 = 1, m2 = 1);
    for(i = 1, #D, my(ap = ellap(E, D[i][1])); if(m1 && !setsearch(Set(S1[i]), ap), m1 = 0); if(m2 && !setsearch(Set(S2[i]), ap), m2 = 0); if(!m1 && !m2, break));
    if(m1, print("psi1 factor: ", e[1], "  ", e[2]));
    if(m2, print("psi2 factor: ", e[1], "  ", e[2])), 1), err, 0))}
quit
