/* MPFI replay of the six-circle all-pair Farkas certificate.
 *
 * The JSON certificate is converted to a line-oriented data file by the
 * accompanying Python script.  All geometric bounds and the final strict
 * comparison are then evaluated with MPFI, using MPFR underneath.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <mpfi.h>
#include <mpfr.h>

#define PREC 256
#define N 6
#define ROWS 30

static void point(mpfi_t x, const char *s) {
  if (mpfi_set_str(x, s, 10) != 0) { fprintf(stderr, "bad decimal: %s\n", s); exit(2); }
}

static void endpoint(mpfr_t out, mpfi_t x, int right) {
  if (right) mpfi_get_right(out, x); else mpfi_get_left(out, x);
}

static void endpoint_point(mpfi_t out, mpfi_t x, int right) {
  mpfr_t t; mpfr_init2(t, PREC); endpoint(t, x, right); mpfi_set_fr(out, t); mpfr_clear(t);
}

static int cmp_right_one(mpfi_t x) {
  mpfr_t r, one; mpfr_inits2(PREC, r, one, (mpfr_ptr)0);
  endpoint(r, x, 1); mpfr_set_ui(one, 1, MPFR_RNDA);
  int v = mpfr_cmp(r, one); mpfr_clears(r, one, (mpfr_ptr)0); return v;
}

static void angle_lower(mpfi_t out, mpfi_t *r, mpfi_t *lo, mpfi_t *hi, int i, int j) {
  mpfi_t d, d2, a, b, aa, bb, num, den, c, c_hi, acosv;
  mpfi_inits2(PREC, d,d2,a,b,aa,bb,num,den,c,c_hi,acosv,(mpfi_ptr)0);
  mpfi_add(d, r[i], r[j]); mpfi_sqr(d2, d);
  mpfi_set_ui(out, 0);
  int have = 0;
  mpfr_t ch, al, old, minus_one, one; mpfr_inits2(PREC, ch,al,old,minus_one,one,(mpfr_ptr)0);
  mpfr_set_si(minus_one, -1, MPFR_RNDD); mpfr_set_ui(one, 1, MPFR_RNDU);
  for (int x = 0; x < 2; ++x) for (int y = 0; y < 2; ++y) {
    endpoint_point(a, x ? hi[i] : lo[i], x ? 1 : 0);
    endpoint_point(b, y ? hi[j] : lo[j], y ? 1 : 0);
    mpfi_sqr(aa, a); mpfi_sqr(bb, b); mpfi_add(num, aa, bb); mpfi_sub(num, num, d2);
    mpfi_mul(den, a, b); mpfi_mul_ui(den, den, 2); mpfi_div(c, num, den);
    mpfi_get_right(ch, c);
    if (mpfr_cmp(ch, one) >= 0) { mpfi_set_ui(out, 0); have = 1; continue; }
    if (mpfr_cmp(ch, minus_one) <= 0) { mpfi_const_pi(acosv); }
    else { mpfi_set_fr(c_hi, ch); mpfi_acos(acosv, c_hi); }
    endpoint(al, acosv, 0); endpoint(old, out, 0);
    if (!have || mpfr_cmp(al, old) < 0) { mpfi_set(out, acosv); have = 1; }
  }
  mpfr_clears(ch,al,old,minus_one,one,(mpfr_ptr)0);
  mpfi_clears(d,d2,a,b,aa,bb,num,den,c,c_hi,acosv,(mpfi_ptr)0);
}

int main(int argc, char **argv) {
  int dump = argc == 3 && strcmp(argv[2], "--dump-angles") == 0;
  if (argc != 2 && !dump) { fprintf(stderr, "usage: %s CERTIFICATE.dat [--dump-angles]\n", argv[0]); return 2; }
  FILE *fp = fopen(argv[1], "r"); if (!fp) { perror(argv[1]); return 2; }
  char rho_s[256]; if (fscanf(fp, "%255s", rho_s) != 1) return 2;
  mpfi_t rho, r[N], lo[N], hi[N], two_pi, pi, total, term, coeff;
  mpfi_inits2(PREC, rho,two_pi,pi,total,term,coeff,(mpfi_ptr)0);
  point(rho, rho_s); mpfi_const_pi(pi); mpfi_mul_ui(two_pi, pi, 2);
  for (int i=0;i<N;++i) { mpfi_init2(r[i], PREC); mpfi_init2(lo[i], PREC); mpfi_init2(hi[i], PREC); mpfi_set_ui(r[i], i+5); mpfi_sqrt(r[i], r[i]); }
  for (int i=0;i<N;++i) {
    mpfi_t u, cand, two; mpfi_inits2(PREC,u,cand,two,(mpfi_ptr)0); mpfi_set_ui(two,2);
    mpfi_sub(u, rho, r[i]); mpfi_set_ui(lo[i], 0);
    for (int j=0;j<N;++j) if (j!=i) { mpfi_mul(cand,r[j],two); mpfi_add(cand,cand,r[i]); mpfi_sub(cand,cand,rho); if (mpfi_cmp(cand,lo[i])>0) mpfi_set(lo[i],cand); }
    mpfi_set(hi[i],u); mpfi_clears(u,cand,two,(mpfi_ptr)0);
  }
  int failures=0;
  for (int rec=0; rec<60; ++rec) {
    int order[N]; char s[256];
    for (int i=0;i<N;++i) if (fscanf(fp, "%d", &order[i]) != 1) return 2;
    char coeffs[ROWS][256];
    for (int k=0;k<ROWS;++k) if (fscanf(fp, "%255s", coeffs[k]) != 1) return 2;
    mpfi_t columns[N]; for (int g=0;g<N;++g) { mpfi_init2(columns[g],PREC); mpfi_set_ui(columns[g],0); }
    mpfi_set_ui(total,0); int k=0;
    if (dump) { printf("ANGLE"); for (int z=0;z<N;++z) printf(" %d",order[z]); }
    for (int a=0;a<N;++a) for (int b=a+1;b<N;++b) {
      mpfi_t ang; mpfi_init2(ang,PREC); angle_lower(ang,r,lo,hi,order[a]-5,order[b]-5);
      if (dump) { mpfr_t dbg; mpfr_init2(dbg,PREC); endpoint(dbg,ang,0); printf(" "); mpfr_out_str(stdout,10,100,dbg,MPFR_RNDD); mpfr_clear(dbg); }
      for (int path=0; path<2; ++path) {
        point(coeff,coeffs[k]); mpfi_mul(term,coeff,ang); mpfi_add(total,total,term);
        int len = path ? (a-b+N) : (b-a);
        for (int t=0;t<len;++t) { int gap = path ? (b+t)%N : (a+t)%N; mpfi_add(columns[gap],columns[gap],coeff); }
        ++k;
      }
      mpfi_clear(ang);
    }
    if (dump) putchar('\n');
    for (int g=0;g<N;++g) if (cmp_right_one(columns[g])>0) { fprintf(stderr,"order %d column %d failed\n",rec,g); failures++; }
    for (int g=0;g<N;++g) mpfi_clear(columns[g]);
    mpfr_t left, right; mpfr_inits2(PREC,left,right,(mpfr_ptr)0); endpoint(left,total,0); endpoint(right,two_pi,1);
    if (!dump && mpfr_cmp(left,right)<=0) { fprintf(stderr,"order %d failed\n",rec); failures++; }
    mpfr_clears(left,right,(mpfr_ptr)0);
  }
  fclose(fp); printf("MPFI replay: %s\n", failures ? "FAILED" : "PASSED (60 orders)"); return failures ? 1 : 0;
}
