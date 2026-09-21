quartic(m) = 4*m^4 + 36480*m^3 - 115540*m^2 + 91200*m + 25;
f = y^2 - (4*x^4 + 36480*x^3 - 115540*x^2 + 91200*x + 25);
E = ellinit(ellfromeqn(f));
print("E ainvs: ", E.a1, " ", E.a2, " ", E.a3, " ", E.a4, " ", E.a6);
D = E.disc;
print("disc(E) = ", D, "  factored: ", factor(D));
countquartic(p) = {my(cnt=0); for(mm=0,p-1, my(v=lift(Mod(quartic(mm),p))); if(v==0, cnt+=1, if(kronecker(v,p)==1, cnt+=2))); if(kronecker(4,p)==1, cnt+=2); return(cnt);};
countE(p) = {return(p+1-ellap(E,p));};
for(i=1,6, myp=prime(30+i); if(Mod(D,myp)!=0, print("p=",myp,"  #quartic=",countquartic(myp),"  #E(Fp)=",countE(myp))));
