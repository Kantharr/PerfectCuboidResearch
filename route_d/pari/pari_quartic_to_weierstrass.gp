/* Y^2 = 4m^4 + 36480m^3 - 115540m^2 + 91200m + 25
   derived for kernel (alpha,beta,gamma)=(5,2,19), ratio (a,b)=(39,37),
   seeded from the t=1 hit (39,37,1) -> u2=4,u3=6. */

f = y^2 - (4*x^4 + 36480*x^3 - 115540*x^2 + 91200*x + 25);
E = ellinit(ellfromeqn(f));
print("Weierstrass ainvs [a1,a2,a3,a4,a6]: ", E.a1, " ", E.a2, " ", E.a3, " ", E.a4, " ", E.a6);
print("Discriminant: ", E.disc);
print("j-invariant: ", E.j);
print("Conductor: ", ellglobalred(E)[1]);
