/* Run route_d_findgens.gp over a list of lines.  Read a params file first defining
     LINES = [[a, b], ...];  FG_OUT = "path/to/knowngens_part.gp";   (optional FG_H1, FG_H2, FG_EFF)
   e.g.  gp -q params.gp route_d_findgens_run.gp
   Each found line is appended to FG_OUT as one KNOWNGENS entry; merge the parts into a file
   KNOWNGENS = [ ... ]; and point ROUTE_D_KNOWNGENS at it.                                    */
\r route_d_findgens.gp
default(parisize, 1000000000);
{
  foreach(LINES, L, my(t = getabstime(), r = iferr(findgens(L[1], L[2]), err, [Str("error ", err), 0, []]));
    print(L[1], ":", L[2], "  ", r[1], "  ", r[2], "  #points ", #r[3], "  (", (getabstime() - t) \ 1000, " s)");
    if(#r[3] && r[1] != "not found" && #r[3] == r[2][1],
      write(FG_OUT, gensentry(L[1], L[2], r[3]))));
}
quit
