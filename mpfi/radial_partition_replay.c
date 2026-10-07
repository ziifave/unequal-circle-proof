/* MPFI replay for a finite radial-box partition of the six-circle cut. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <mpfi.h>
#include <mpfr.h>

#define PREC 256
#ifndef N
#define N 6
#endif
#ifndef START
#define START 5
#endif
#define ROWS (N*(N-1))

static void point(mpfi_t x, const char *s) {
  if (mpfi_set_str(x, s, 10) != 0) { fprintf(stderr, "bad decimal: %s\n", s); exit(2); }
}
static void ep(mpfr_t out, mpfi_t x, int right) {
  if (right) mpfi_get_right(out, x); else mpfi_get_left(out, x);
}
static void endpoint_point(mpfi_t out, mpfi_t x, int right) {
  mpfr_t t; mpfr_init2(t, PREC); ep(t, x, right); mpfi_set_fr(out, t); mpfr_clear(t);
}
static void print_endpoint(mpfi_t x, int right) {
  mpfr_t t; mpfr_init2(t, PREC); ep(t, x, right); mpfr_out_str(stdout, 10, 100, t, MPFR_RNDD); mpfr_clear(t);
}
static void angle_lower(mpfi_t out, mpfi_t *r, mpfi_t *lo, mpfi_t *hi, int i, int j) {
  mpfi_t d,d2,a,b,aa,bb,num,den,c,ch,ac;
  mpfi_inits2(PREC,d,d2,a,b,aa,bb,num,den,c,ch,ac,(mpfi_ptr)0);
  mpfi_add(d,r[i],r[j]); mpfi_sqr(d2,d); mpfi_set_ui(out,0); int have=0;
  mpfr_t cr,al,old,m1,one; mpfr_inits2(PREC,cr,al,old,m1,one,(mpfr_ptr)0);
  mpfr_set_si(m1,-1,MPFR_RNDD); mpfr_set_ui(one,1,MPFR_RNDU);
  for(int x=0;x<2;x++) for(int y=0;y<2;y++) {
    endpoint_point(a,x?hi[i]:lo[i],x?1:0); endpoint_point(b,y?hi[j]:lo[j],y?1:0);
    mpfi_sqr(aa,a); mpfi_sqr(bb,b); mpfi_add(num,aa,bb); mpfi_sub(num,num,d2);
    mpfi_mul(den,a,b); mpfi_mul_ui(den,den,2); mpfi_div(c,num,den); mpfi_get_right(cr,c);
    if(mpfr_cmp(cr,one)>=0) { mpfi_set_ui(out,0); have=1; continue; }
    if(mpfr_cmp(cr,m1)<=0) mpfi_const_pi(ac);
    else { mpfi_set_fr(ch,cr); mpfi_acos(ac,ch); }
    ep(al,ac,0); ep(old,out,0);
    if(!have || mpfr_cmp(al,old)<0) { mpfi_set(out,ac); have=1; }
  }
  mpfr_clears(cr,al,old,m1,one,(mpfr_ptr)0);
  mpfi_clears(d,d2,a,b,aa,bb,num,den,c,ch,ac,(mpfi_ptr)0);
}
static void emit_orders(int *o, int pos, int *used, FILE *fp, mpfi_t *r, mpfi_t *base_lo, mpfi_t *base_hi, int split) {
  if(pos==N) {
    if(o[1]>o[N-1]) return;
    int total=(int)1; for(int z=0;z<N;z++) total*=split;
    int idx[N];
    for(int code=0;code<total;code++) {
      int q=code; mpfi_t lo[N],hi[N],step,tmp;
      for(int i=0;i<N;i++){mpfi_init2(lo[i],PREC);mpfi_init2(hi[i],PREC);}
      mpfi_inits2(PREC,step,tmp,(mpfi_ptr)0);
      for(int i=0;i<N;i++) {
        idx[i]=q%split; q/=split;
        mpfi_sub(tmp,base_hi[i],base_lo[i]); mpfi_div_ui(step,tmp,split);
        mpfi_mul_ui(tmp,step,idx[i]); mpfi_add(lo[i],base_lo[i],tmp);
        mpfi_mul_ui(tmp,step,idx[i]+1); mpfi_add(hi[i],base_lo[i],tmp);
      }
      fprintf(fp,"CELL"); for(int i=0;i<N;i++) fprintf(fp," %d",o[i]);
      for(int i=0;i<N;i++){fprintf(fp," ");print_endpoint(lo[i],0);fprintf(fp," ");print_endpoint(hi[i],1);}
      for(int a=0;a<N;a++) for(int b=a+1;b<N;b++) {
        mpfi_t ang; mpfi_init2(ang,PREC); angle_lower(ang,r,lo,hi,o[a]-START,o[b]-START);
        fprintf(fp," "); print_endpoint(ang,0); fprintf(fp," ");
        mpfi_clear(ang);
      }
      fprintf(fp,"\n");
      mpfi_clears(step,tmp,(mpfi_ptr)0); for(int i=0;i<N;i++){mpfi_clear(lo[i]);mpfi_clear(hi[i]);}
    }
    return;
  }
  for(int v=START;v<START+N;v++) if(!used[v-START]) { used[v-START]=1;o[pos]=v;emit_orders(o,pos+1,used,fp,r,base_lo,base_hi,split);used[v-START]=0; }
}
static void rows_for(int rows[ROWS][N]) {
  int k=0;
  for(int a=0;a<N;a++) for(int b=a+1;b<N;b++) for(int path=0;path<2;path++) {
    for(int g=0;g<N;g++) rows[k][g]=0;
    int len=path?(a-b+N):(b-a);
    for(int t=0;t<len;t++){int g=path?(b+t)%N:(a+t)%N; rows[k][g]=1;}
    k++;
  }
}
int main(int argc,char **argv) {
  int is_dump=argc==4 && strcmp(argv[3],"--dump")==0;
  if((!is_dump && argc!=2) || (is_dump && argc!=4)){fprintf(stderr,"usage: %s RHO SPLIT --dump\n       %s DATA\n",argv[0],argv[0]);return 2;}
  if(is_dump) {
    mpfi_t rho,r[N],lo[N],hi[N],two,cand; mpfi_inits2(PREC,rho,two,cand,(mpfi_ptr)0);
    point(rho,argv[1]); mpfi_set_ui(two,2);
    for(int i=0;i<N;i++){mpfi_init2(r[i],PREC);mpfi_init2(lo[i],PREC);mpfi_init2(hi[i],PREC);mpfi_set_ui(r[i],i+START);mpfi_sqrt(r[i],r[i]);}
    for(int i=0;i<N;i++){mpfi_sub(hi[i],rho,r[i]);mpfi_set_ui(lo[i],0);for(int j=0;j<N;j++)if(i!=j){mpfi_mul_ui(cand,r[j],2);mpfi_add(cand,cand,r[i]);mpfi_sub(cand,cand,rho);if(mpfi_cmp(cand,lo[i])>0)mpfi_set(lo[i],cand);}}
    int o[N],used[N]={0}; o[0]=START; used[0]=1; emit_orders(o,1,used,stdout,r,lo,hi,atoi(argv[2])); return 0;
  }
  FILE *fp = strcmp(argv[1], "-") == 0 ? stdin : fopen(argv[1],"r");
  if(!fp){perror(argv[1]);return 2;}
  char tag[16],rho_s[256]; int cells;
  if(fscanf(fp,"%15s %255s %d",tag,rho_s,&cells)!=3 || strcmp(tag,"RHO")!=0){fprintf(stderr,"bad header\n");return 2;}
  mpfi_t rho,r[N],two_pi,total,term,coeff; mpfi_inits2(PREC,rho,two_pi,total,term,coeff,(mpfi_ptr)0); point(rho,rho_s); mpfi_t pi;mpfi_init2(pi,PREC);mpfi_const_pi(pi);mpfi_mul_ui(two_pi,pi,2);
  for(int i=0;i<N;i++){mpfi_init2(r[i],PREC);mpfi_set_ui(r[i],i+START);mpfi_sqrt(r[i],r[i]);}
  int rows[ROWS][N]; rows_for(rows); int failures=0;
  for(int rec=0;rec<cells;rec++){
    if(fscanf(fp,"%15s",tag)!=1 || strcmp(tag,"CELL")!=0)return 2;
    int o[N];mpfi_t lo[N],hi[N];
    for(int i=0;i<N;i++){if(fscanf(fp,"%d",&o[i])!=1)return 2;}
    for(int i=0;i<N;i++){mpfi_init2(lo[i],PREC);mpfi_init2(hi[i],PREC);char a[256],b[256];if(fscanf(fp,"%255s %255s",a,b)!=2)return 2;point(lo[i],a);point(hi[i],b);}
    mpfi_t columns[N];for(int i=0;i<N;i++){mpfi_init2(columns[i],PREC);mpfi_set_ui(columns[i],0);}mpfi_set_ui(total,0);int k=0;
    for(int a=0;a<N;a++)for(int b=a+1;b<N;b++){mpfi_t ang;mpfi_init2(ang,PREC);angle_lower(ang,r,lo,hi,o[a]-START,o[b]-START);for(int path=0;path<2;path++){char cs[256];if(fscanf(fp,"%255s",cs)!=1)return 2;point(coeff,cs);mpfi_mul(term,coeff,ang);mpfi_add(total,total,term);for(int g=0;g<N;g++)if(rows[k][g])mpfi_add(columns[g],columns[g],coeff);k++;}mpfi_clear(ang);}
    for(int g=0;g<N;g++){mpfr_t x,one;mpfr_inits2(PREC,x,one,(mpfr_ptr)0);ep(x,columns[g],1);mpfr_set_ui(one,1,MPFR_RNDU);if(mpfr_cmp(x,one)>0){fprintf(stderr,"cell %d column %d failed\n",rec,g);failures++;}mpfr_clears(x,one,(mpfr_ptr)0);mpfi_clear(columns[g]);}
    mpfr_t x,y;mpfr_inits2(PREC,x,y,(mpfr_ptr)0);ep(x,total,0);ep(y,two_pi,1);if(mpfr_cmp(x,y)<=0){fprintf(stderr,"cell %d failed\n",rec);failures++;}mpfr_clears(x,y,(mpfr_ptr)0);for(int i=0;i<N;i++){mpfi_clear(lo[i]);mpfi_clear(hi[i]);}
  }
  if(fp != stdin) fclose(fp);
  printf("MPFI radial-partition replay: %s (%d cells)\n",failures?"FAILED":"PASSED",cells);
  return failures?1:0;
}
