
#define max(a,b) ((a)>(b) ? (a) : (b))

int LDBG = 1;  // FIXME s/b 0
#define DELTA_COEFF 400.0
#define MINIMUM_DELTA 0.02
#define UPDATE_THRESH 50.0

#define DISTBEGIN 14
#define DISTLENG  25
#define MAXPARS (37 + DISTBEGIN)

const char* parnames[MAXPARS+1] = {  // "+1" to allow comma at end
 "NoRule", "OverComma", "Pred2Noun", "FollowComma", "NonGaNonVerb",
 "HaNoTerm", "HaSemiTerm", "NounNoun", "ParLvl", "Com2Nocom",
 "termOri", "adjRenyou", "adnomNo", "quotingTo",
 "DistNo2",  "DistNo4",  "DistNo9", "DistNo14",  "DistNo19",
 "DistHa2",  "DistHa4",  "DistHa9", "DistHa14",  "DistHa19",
 "DistNoun2",  "DistNoun4",  "DistNoun9", "DistNoun14",  "DistNoun19",
 "DistPred2",  "DistPred4",  "DistPred9", "DistPred14",  "DistPred19",
 "DistAny2",  "DistAny4",  "DistAny9", "DistAny14",  "DistAny19",
 "GaCost2", "GaCost3", "GaCost4", "GaCost5", 
 "WoCost2", "WoCost3", "WoCost4", "WoCost5",
 "NiCost2", "NiCost3", "NiCost4", "NiCost5",
};

eval_t* paradrs[MAXPARS+1] = {
  &COST_AGAINST_RULE, &COST_OVER_COMMA,
       &COST_HA_TO_PRED2NOUN, &COST_FOLLOW_COMMA,
       &COST_NON_GA_TO_NONVERB, &COST_HA_NOTERM, &COST_HA_SEMITERM,
       &COST_NOUN_NOUN, &COST_PAREN_LVL,
       &COST_COMMA2NOCOMMA, &COST_TERM_ORI, 
       &COST_ADJ_RENYOU, &COST_ADNOMNO_NONOUN,
       &COST_QUO_TO_LVL,
  &distCostTable[0][2], &distCostTable[0][4], &distCostTable[0][9],
    &distCostTable[0][14], &distCostTable[0][19],
  &distCostTable[1][2], &distCostTable[1][4], &distCostTable[1][9],
    &distCostTable[1][14], &distCostTable[1][19],
  &distCostTable[2][2], &distCostTable[2][4], &distCostTable[2][9],
    &distCostTable[2][14], &distCostTable[2][19],
  &distCostTable[3][2], &distCostTable[3][4], &distCostTable[3][9],
    &distCostTable[3][14], &distCostTable[3][19],
  &distCostTable[4][2], &distCostTable[4][4], &distCostTable[4][9],
    &distCostTable[4][14], &distCostTable[4][19],
  &nGaCostTable[2], &nGaCostTable[3], &nGaCostTable[4], &nGaCostTable[5],
  &nWoCostTable[2], &nWoCostTable[3], &nWoCostTable[4], &nWoCostTable[5],
  &nNiCostTable[2], &nNiCostTable[3], &nNiCostTable[4], &nNiCostTable[5],
};


bool needInterpolation(int a) {
 return (DISTBEGIN <= a && a < DISTBEGIN+DISTLENG);
}

 //****

void interpolate() {
 forr(i, 0, 4) {
   distCostTable[i][3] = (distCostTable[i][2] + distCostTable[i][4]) / 2;
   distCostTable[i][5] = (4*distCostTable[i][4] + 1*distCostTable[i][9]) / 5;
   distCostTable[i][6] = (3*distCostTable[i][4] + 2*distCostTable[i][9]) / 5;
   distCostTable[i][7] = (2*distCostTable[i][4] + 3*distCostTable[i][9]) / 5;
   distCostTable[i][8] = (1*distCostTable[i][4] + 4*distCostTable[i][9]) / 5;
   distCostTable[i][10] = (4*distCostTable[i][9] + 1*distCostTable[i][14]) /5;
   distCostTable[i][11] = (3*distCostTable[i][9] + 2*distCostTable[i][14]) /5;
   distCostTable[i][12] = (2*distCostTable[i][9] + 3*distCostTable[i][14]) /5;
   distCostTable[i][13] = (1*distCostTable[i][9] + 4*distCostTable[i][14]) /5;
   distCostTable[i][15] = (4*distCostTable[i][14] + 1*distCostTable[i][19])/5;
   distCostTable[i][16] = (3*distCostTable[i][14] + 2*distCostTable[i][19])/5;
   distCostTable[i][17] = (2*distCostTable[i][14] + 3*distCostTable[i][19])/5;
   distCostTable[i][18] = (1*distCostTable[i][14] + 4*distCostTable[i][19])/5;
   forr(j, 20, 63)
     distCostTable[i][j] = distCostTable[i][19];
 }
}

 //****

#define MAXLINES 5000
int curline = 0, nlines = 0;
int answers[MAXLINES][MAXCHUNKS];

void readAnswers() {
 FILE* fp = fopen("ans.out", "r");
 if (fp == NULL) {
   printf("answer file not found\n" );
   exit(8);
 }

 char buf[900];

 while(fgets(buf, 888, fp)) {
   if (LDBG) printf("ans %d:", nlines);
   int d[MAXCHUNKS], n;
   n = sscanf(buf, 
"%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d",
&d[0], &d[1], &d[2], &d[3], &d[4], &d[5], &d[6], &d[7], &d[8], &d[9],
&d[10], &d[11], &d[12], &d[13], &d[14], &d[15], &d[16], &d[17], &d[18], &d[19],
&d[20], &d[21], &d[22], &d[23], &d[24], &d[25], &d[26], &d[27], &d[28], &d[29],
&d[30], &d[31], &d[32], &d[33], &d[34], &d[35], &d[36], &d[37], &d[38], &d[39],
&d[40], &d[41], &d[42], &d[43], &d[44], &d[45], &d[46], &d[47], &d[48], &d[49],
&d[50], &d[51], &d[52], &d[53], &d[54], &d[55], &d[56], &d[57], &d[58], &d[59],
&d[60], &d[61], &d[62], &d[63]
   );
   forr(i, 0, n-1) {
     answers[nlines][i] = (d[i]==99 ? -1 : d[i]);
     //if (LDBG) printf(" %d", answers[nlines][i]);
   }
   if (LDBG) printf("\n");
   nlines++;
 } // while fgets
}

 //****

void readEvalParam() {
 char buf[50];
 char str[30];
 float f;
 char fname[200] = "kakeval.txt";
 char* s;
 if ((s = getenv("KAKAROT_EVAL_INIT_FILE")))
   strcpy(fname, s);
 FILE* fp = fopen(fname, "r");
 if (fp == NULL) {
   printf("eval init file not found: %s\n", fname);
   exit(8);
 }
 while(fgets(buf, 50, fp)) {
   sscanf(buf, "%s %f", str, &f);
   forr(i, 0, MAXPARS-1) {
     if (!strcmp(parnames[i], str)) {
       *paradrs[i] = f;
       if (LDBG) printf("set: %d(%s) to: %f\n", i, str, f);
       break;
     }
   }
 } // while fgets

 interpolate();


 readAnswers();
}

 //****

eval_t curvalAry[MAXLINES];
eval_t bestvalAry[MAXLINES];
eval_t d4curAry[MAXLINES][MAXPARS+1];
eval_t d4bestAry[MAXLINES][MAXPARS+1];
eval_t newpars[MAXPARS+1];

void kakPostProcess() {
 eval_t* d4cur  = &d4curAry[curline][0];
 eval_t* d4best = &d4bestAry[curline][0];
 int bestpath[MAXCHUNKS];

if (LDBG)
 printf("++++ kak learn step begin line %d/%d ++++\n", curline, nlines); //**

 // 正解のパスを読み込む

 forr(i, 0, nChunk-1) {
   int d = answers[curline][i];
   bestpath[i] = (d==99 ? -1 : d);
 }

 // 正答、誤答数を数えて出力

 bestlinks[nChunk-3][nChunk-2] = nChunk - 1;
 //bestlinks[nChunk-3][nChunk-1] = -1;
 int* kakans = &bestlinks[nChunk-3][0];
 int nok = 0, nng = 0;
 forr(i, 0, nChunk-2)
   if (kakans[i] != bestpath[i] && bestpath[i] != -1) nng++;
   else
   if (kakans[i] == bestpath[i] && bestpath[i] != -1) nok++;
 printf("summary: line %d ok %d ng %d\n", curline, nok, nng);

 // 正解を出してたら何もせずに終了

 bool mch = true;
 forr(i, 0, nChunk-1)
   if (bestlinks[nChunk-3][i] != bestpath[i] && bestpath[i] != -1) {
     mch = false;
     break;
   }
 if (mch) {
   if (LDBG) printf("results matched, learning skipped\n");
   curline++;
   return;
 }

if (LDBG) {
 printf("cur/best paths:\n"); //********
 forr(i, 0, nChunk-1)
   if (LDBG) printf("%d/%d ", bestlinks[nChunk-3][i], bestpath[i]);
 printf("\n"); //********
}

 // kakarotの出したベストパスを設定・評価

 forr(i, 0, nChunk-1)
   semChunks[i].clrDpnd();
 
 semChunks[nChunk-1].hop = 0;

 forv(i, nChunk-2, 0) {
   assert(bestlinks[nChunk-3][i] != 99 &&
          bestlinks[nChunk-3][i] != -1   );
   makedep(i, bestlinks[nChunk-3][i]);
 }

//EDBG = 1;  // enable output  FIXME?  appropriate?

 eval_t curval = eval();
 curvalAry[curline] = curval;
if (LDBG) printf("curval %f\n", curval); //********


if (LDBG) printf("++++++++ kak path done.  now bestans... ++++++++\n"); //**

 // 正解のパスを設定

 forr(i, 0, nChunk-1)
   semChunks[i].clrDpnd();
 
 semChunks[nChunk-1].hop = 0;

 forv(i, nChunk-2, 0) {
   assert(bestpath[i]!=99);
   makedep(i, bestpath[i] == -1 ? bestlinks[nChunk-3][i] : bestpath[i]);
                  // FIXME -1のときのデフォルトが交差したらどうする？？
 }

 eval_t bestval = eval();
 bestvalAry[curline] = bestval;
if (LDBG) printf("bestval %f\n", bestval); //********
if (LDBG) printf("best-cur diff %f line %d\n", bestval-curval, curline); //****

 if (bestval < curval + 0.0001) {  // allow for some rounding error
   //fflush(0);
   //assert(0);
   printf("WARNING: line %d : bestval oddly small, skip learning\n", curline);
   curvalAry[curline] = bestvalAry[curline] = 0;  // would suppress side effect
   curline++;
   return;
 }

 curline++;
}

