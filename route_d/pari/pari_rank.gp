f = y^2 - (4*x^4 + 36480*x^3 - 115540*x^2 + 91200*x + 25);
E = ellinit(ellfromeqn(f));
print("E: y^2 = x^3 + ", E.a2, "*x^2 + ", E.a4, "*x + ", E.a6);
print("Conductor: ", ellglobalred(E)[1]);
print("Torsion: ", elltors(E));
r = ellrank(E, 4);
print("ellrank output [r1,r2,s,points]: ", r);
