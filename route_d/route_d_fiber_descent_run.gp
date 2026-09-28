/* Run route_d_fiber_descent.gp over a list of fibres.  Put  FIBRES = [[a,b,al,be,ga], ...];  in a
   params file read first:  gp -q params.gp route_d_fiber_descent_run.gp                          */
\r route_d_fiber_descent.gp
default(parisize, 1000000000);
{foreach(FIBRES, f, my(t0 = getabstime(), r = iferr(fiberdescent(f[1], f[2], f[3], f[4], f[5]), err, ["ERROR", Str(err)]));
   print(f, "  ", r, "  (", (getabstime() - t0) \ 1000, " s)"))}
quit
