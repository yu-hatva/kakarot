#include <assert.h>
 // for uint64_t
#include <stdint.h>
 // for memset
#include <string.h>
 // for max
#include <algorithm>

#include "param.h"

#define forr(i,m,n) for(int i=(m); i<=(n); i++)
#define forv(i,m,n) for(int i=(m); i>=(n); i--)

int EDBG = 0;
#define EDBGE (1 && EDBG)
int CMP_CABOCHA = 0;

namespace CaboCha {

#define MAXCHUNKS 64
#define MAXTOKENS 256
Chunk* cabChunks[MAXCHUNKS];  // cabochaのデータ構造へのポインタ
int nChunk;  // tree->chunk_size() をセットしとく

/*
* a) 可能な係り先の列挙
* 
* 文末の倒置可能性については後ほど対処。今は必ず右に係るとする。
* 
* 以下のクライテリアにしたがって、各文節について可能な係り先文節を列挙する。
* 品詞情報だけから、テーブル引くだけで決める。テーブルはファイルから読み込む。
* 
* 文節末の品詞が：
* ・連体詞　-> 名詞 <連体修飾>
* ・副詞   -> 動詞・形容[動]詞・副詞・（一部の？）連体詞 <連用修飾>
* ・名詞   -> (格/係助詞が略されてると思い）述語[動詞/形容<動>詞/名詞＋ダ] <補語>
* ・動詞・形容[動] 連体形 -> 名詞  <連体節：連体修飾>
* ・動詞・形容[動] 連用形 -> 動詞・形容[動]詞 <複文、並列>
* ・動詞・形容[動] 終止形・命令形 ->  <文末?>
* 　　　　※未然形（食わない）、仮定形（食えば）は必ず助詞が後につくはず
* ・接続詞 -> 述語（文の最後の？）
* ・感動詞 -> ?? <N/A 無視してよい?>
* 
* ・助詞 --+-- 格助詞  -> 述語[動詞/形容<動>詞/名詞＋ダ]  <補語>
*         +-- 係助詞  -> 述語[動詞/形容<動>詞/名詞＋ダ]  <補語?>
*         +--  接続助詞  ->  動詞・形容[動]詞 <複文>
*         +-- 副助詞   -> ?? <連用修飾?>
*         +--  終助詞  -> <文末?>
*         +-- 並立助詞 -> 名詞<名詞並立>、 動詞/形容<動>詞<述語並立>
*         +--  特殊(に、に[副詞化]、の[連体化]、と[副詞化]、にゃ、かな、けむ、ん)
* 
* ・助動詞 連体形 -> 名詞  <連体節：連体修飾>
* 　　　　 連用形 -> 動詞・形容[動]詞 <複文、並列>
* 
* 結局、全品詞を可能な係り先によって　１）名詞　２）述語　３）全て　に分ける。
* 
* b) 探索
* 
* 文末側から、可能な組み合わせについて係り受け木を作っていく。各木（状態）に対して
* 対応する意味データ構造を作成し、評価値（コスト/損失）を求める。値最小のものを選ぶ。
* 評価値は、木が大きくなると単調に増加するとして（そのようにコスト関数を決める）、
* 途中の部分木で現在までの最善値を越えたらそこでその枝は刈る。
* 
* まず各文節に対し、主辞・機能辞（接続辞）・格辞を判定する。
* 主辞・機能辞はcabochaと同じ。kakarotでは機能辞でなく「接続辞」と呼ぶ（格辞と区別）。
* 格辞は、文節中の*最初の*格/係/副助詞。「…にも」なら「に」が格辞、「も」が接続辞。
*/

//******************************************
// struct chunkBitmapC, chunkItorC 文節セットとそのイテレータ

struct chunkBitmapC {
  // 注意：文節０はLSB、つまり日本語の並びと反対
  // FIXME? size(nChunk)も持たせる方がよいか？
 uint64_t v;
 chunkBitmapC(uint64_t u = 0LL) : v(u) {}
 void init() { v = 0LL; }
 void set(int i) { v |= 1LL << i; }
 void clr(int i) { v &= ~(1LL << i); }
 bool get(int i) const { return ((v & (1LL << i)) != 0LL); }
 bool empty() const { return (v == 0LL); }

 chunkBitmapC operator ~() const { return chunkBitmapC(~v); }
 chunkBitmapC operator &(chunkBitmapC c) const
    { return chunkBitmapC(v & c.v); }
 chunkBitmapC operator |(chunkBitmapC c) const
    { return chunkBitmapC(v | c.v); }

 void operator |=(chunkBitmapC c) { v |= c.v; }

 static chunkBitmapC range(int i, int j)
    { return chunkBitmapC(((1LL << (j-i+1)) - 1LL) << i); }
};

struct chunkItorC {
  // FIXME 文節数 MAX 64 を仮定している
 int cur;
 chunkBitmapC bm;

 chunkItorC (chunkBitmapC b) : bm(b) {
   cur = -1;
   ++(*this); // 最初の'1'を探す。なければ64
 }

 void operator ++() {  // 今のcurの次の'1'を探す。なければ64
   for(cur++; cur<64; cur++)
     if (bm.get(cur))
       break;
 }

 bool atEnd() const { return (cur >= 64); }
};

//******************************************
// struct semChunkC 文節データ構造

#define MAXSRC 16

struct semChunkC {
  Chunk* buddy() const { return cabChunks[suf()]; } // 対応するcabocha文節
  int suf() const;  // このエントリのID
  int caseTokenID;  // 格辞の形態素位置
                  // 主辞、接続辞は… buddy()からたどればわかるはず（？）
  int cabLink;    // cabochaが回答した係り先（比較用）
  int nSrces;         // 係り元の個数
  int srces[MAXSRC];  // 係り元
  int dst;            // 係り先
  int hop;            // ルートから数えた係り段数

  int flags;          // 各種フラグ記憶場所　以下参照
  enum { FG_PREFER_NOUN  =    2, FG_PREFER_PRED =    4, 
         FG_IS_NOUN      =    8, FG_IS_PRED     = 0x10,
         FG_HAS_ADNOM_NO = 0x20, FG_HAS_HA      = 0x40,
         FG_HAS_GA       = 0x80, FG_HAS_WO     = 0x100,
         FG_HAS_NI      = 0x200, FG_HAS_COMMA  = 0x400,
         FG_HAS_PARA    = 0x800, FG_IS_SOLOCONJ_INTERJ = 0x1000,
         FG_IS_PRED2NOUN = 0x2000, FG_HAS_TERMINATION = 0x4000,
         FG_HAS_L_PAREN = 0x8000, FG_HAS_R_PAREN = 0x10000,
         FG_HAS_L_QUOTE = 0x20000, FG_HAS_R_QUOTE = 0x40000,
         FG_HAS_TO    = 0x80000, FG_HAS_DE     = 0x100000,
         FG_HAS_MO   = 0x200000, FG_IS_VERB  = 0x400000,
         FG_HAS_POSTP_CONN =  0x800000,
         FG_HAS_POSTP_TERM = 0x1000000,
         FG_IS_CONJ = 0x2000000, FG_HAS_AUXIL = 0x4000000,
         FG_HAS_POSTP = 0x8000000,
       };

  void build(Tree*); // 文節の各種情報セットアップ
  void reset() { memset(this, 0, sizeof(*this)); }

  void setPreferNoun() { flags |= FG_PREFER_NOUN; }
  void setPreferPred() { flags |= FG_PREFER_PRED; }

  bool preferNoun() const // 係り先は名詞
    { return ((flags & FG_PREFER_NOUN) != 0); } 

  bool preferPred() const  // 係り先は述語
    { return ((flags & FG_PREFER_PRED) != 0); }

  bool preferAny() const   // 係り先は何でも可
    {return (!preferNoun() && !preferPred());}

  bool isNoun() const      // 主辞が名詞
    { return ((flags & FG_IS_NOUN) != 0); }

  bool isVerb() const      // 主辞が動詞
    { return ((flags & FG_IS_VERB) != 0); }

  bool isPred() const  // 主辞が述語（動詞|形容[動]詞|名詞+ダ）
    { return ((flags & FG_IS_PRED) != 0); }
    
  bool hasAdnomNO() const // 連体の「の」あり - caseTokenからわかるか？
    { return ((flags & FG_HAS_ADNOM_NO) != 0); }

  bool hasHA() const  // 「は」あり - caseTokenからわかるか？
    { return ((flags & FG_HAS_HA) != 0); }

  bool hasGA() const // 「が」あり
    { return ((flags & FG_HAS_GA) != 0); } 

  bool hasWO() const  // 「を」あり
    { return ((flags & FG_HAS_WO) != 0); }

  bool hasNI() const // 「に」あり
    { return ((flags & FG_HAS_NI) != 0); } 

  bool hasDE() const // 「で」あり
    { return ((flags & FG_HAS_DE) != 0); } 

  bool hasTO() const // 「と」あり
    { return ((flags & FG_HAS_TO) != 0); } 

  bool hasMO() const // 「も」あり
    { return ((flags & FG_HAS_MO) != 0); } 

  bool hasNonGACase() const // 「が」以外の格あり
    { return ((flags & (FG_HAS_MO|FG_HAS_TO|FG_HAS_DE|FG_HAS_WO)) != 0); } 

  bool hasPostpConn() const    // 接続助詞あり
    { return ((flags & FG_HAS_POSTP_CONN) != 0); }

  bool hasPostpTerm() const    // 終助詞あり
    { return ((flags & FG_HAS_POSTP_TERM) != 0); }

  bool hasPostp() const    // 助詞あり
    { return ((flags & FG_HAS_POSTP) != 0); }

  bool hasAuxil() const    // 助動詞あり
    { return ((flags & FG_HAS_AUXIL) != 0); }

  bool hasComma() const    // コンマあり
    { return ((flags & FG_HAS_COMMA) != 0); }

  bool hasTermination() const    // 文末記号あり
    { return ((flags & FG_HAS_TERMINATION) != 0); }

  // TBC [LR]PAREN/QUOTEは未

  bool hasPara() const    // 並立助詞あり
    { return ((flags & FG_HAS_PARA) != 0); }

  bool isConj() const    // 接続詞あり
    { return ((flags & FG_IS_CONJ) != 0); }

  bool isSoloConjInterj() const    // ソロ接続詞 or 感動詞あり
    { return ((flags & FG_IS_SOLOCONJ_INTERJ) != 0); }

  bool isPred2Noun() const    // 連体形の述語
    { return ((flags & FG_IS_PRED2NOUN) != 0); }

  bool playAsNoun() const {  // 述語が格補語（？）になっている
    return isPred() && hasPostp() && !hasPostpConn() && !hasPostpTerm();
  }
};

semChunkC semChunks[MAXCHUNKS];
int semChunkC::suf() const { return (this - semChunks); }

//******************************************
//  semChunkC::build() 文章の情報を文節データ構造へセット

    // copied from selector.cpp

static inline const char *get_token(const Token *token, size_t id) {
  if (token->feature_list_size <= id) {
    return 0;
  }
  if (std::strcmp("*", token->feature_list[id]) == 0) {
    return 0;
  }
  return token->feature_list[id];
}

void semChunkC::build(Tree* tree) {  // 文節の各種情報セットアップ
 reset();
 Chunk* cabch = buddy();
 int tkStt = cabch->token_pos;    // この文節の開始トークン位置
 int tkEnd = tkStt + cabch->token_size - 1; // ラストトークン位置

  // 格辞を探す  FIXME findCase()とかにまとめる？
 caseTokenID = -1;
 forr(i, tkStt, tkEnd) {
   const char* pos = get_token(tree->token(i), 0); //辞書位置0:品詞
     // 当面、助詞すべて。FIXME 細分化すべきか？
   if (!strcmp(pos, "助詞")) {
     caseTokenID = i;
     break;
   }
 }

  // この文節の主辞・接続辞・格辞
 const Token* thead = tree->token(tkStt + cabch->head_pos);
 const Token* tconn = tree->token(tkStt + cabch->func_pos);
 const Token* tcase = caseTokenID<0 ? tconn : tree->token(caseTokenID);

  // 各種フラグをセット
 flags = 0;

 const char* h0 = get_token(thead, 0);
 const char* h1 = get_token(thead, 1);
 const char* c1 = get_token(tconn, 1);  // NOTE could be NULL
 const char* a1 = get_token(tcase, 1);

 if (!strcmp(h0, "名詞") ||
     !strcmp(h0, "助詞")   )  // 9/13/2012 (IPAでは?)助詞が主辞になることあり
   flags |= FG_IS_NOUN;     // 異常な|ほど|  言った|ものの|  大体形式名詞の
                            // ようなのでとりあえず名詞扱いにしてみる
 forr(i, tkStt, tkEnd) {
   const char* tok = tree->token(i)->normalized_surface;
   if (!strcmp(tok, "、"))   // コンマはラストとは限らない　彼は|そうだ、と|言って
     flags |= FG_HAS_COMMA;

   if (!strcmp(tok, "。") ||
       !strcmp(tok, "？") ||
       !strcmp(tok, "！")   )
     flags |= FG_HAS_TERMINATION;

     // TEMP FIX 9/13/2012 「繰り返すように」「見落としてしまうのではないか」
     // などは一文節で、(cabochaでは)主辞が名詞になってしまう。文節中の
     // どこかに自立動詞があったら述語属性を立てる
     // 「サ変名詞＋する」も含む
   if (!strcmp(get_token(tree->token(i), 0), "動詞") &&
       !strcmp(get_token(tree->token(i), 1), "自立")   )
     flags |= FG_IS_PRED | FG_IS_VERB;

   if (!strcmp(get_token(tree->token(i), 0), "助動詞"))
     flags |= FG_HAS_AUXIL;

   if (!strcmp(get_token(tree->token(i), 0), "助詞"))
     flags |= FG_HAS_POSTP;

 }

 if ((unsigned)tkEnd == tree->token_size() - 1)
     flags |= FG_HAS_TERMINATION;

 bool hasConn =  c1 && !strcmp(c1, "接続助詞");
 if (hasConn)
     flags |= FG_HAS_POSTP_CONN;

 bool hasTerm =  c1 && !strcmp(c1, "終助詞");
 if (hasTerm)
     flags |= FG_HAS_POSTP_TERM;

if (EDBG)
 printf("in semCh:build, suf=%d pos=%s tok=%s##\n", suf(), h0,
          tree->token(cabChunks[suf()]->token_pos)->normalized_surface);

 //if (!strcmp(get_token(thead, 0), "動詞")   ||  サ変抜ける！isVerb()使う
 if (isVerb() ||
     !strcmp(get_token(thead, 0), "形容詞") ||
     !strcmp(get_token(thead, 0), "名詞") &&    // 名詞+ダ(助動詞) / 形容動詞
       (h1 && !strcmp(h1, "形容動詞語幹") && hasAuxil() ||
        hasConn || hasTerm ||
        !strcmp(get_token(tconn, 0), "助動詞")     )  // FIXME? 正しい?
    ) {
   flags |= FG_IS_PRED;
   forr(i, tkStt, tkEnd) {
     const char* t5 = get_token(tree->token(i), 5);
     if ((t5 && strstr(t5, "体言接続") ||
          t5 && strstr(t5, "基本形"))&& //基本,連体で文節未完なら連体形(のはず)
            !(hasTermination() || hasConn || hasTerm))
       flags |= FG_IS_PRED2NOUN;
   }
      // 述語の文節に係・格助詞がついてたら、名詞化されてるはず「その奥深くに」
   if (playAsNoun())
     flags |= FG_IS_NOUN;
 }

 if (!strcmp(tconn->surface, "は") ||
     !strcmp(tcase->surface, "は")   )
   flags |= FG_HAS_HA;

 if (!strcmp(tconn->surface, "が") ||
     !strcmp(tcase->surface, "が")   )
   flags |= FG_HAS_GA;

 if (!strcmp(tconn->surface, "を") ||
     !strcmp(tcase->surface, "を")   )
   flags |= FG_HAS_WO;

 if (!strcmp(tconn->surface, "に") ||
     !strcmp(tcase->surface, "に")   )
   flags |= FG_HAS_NI;

 if (!strcmp(tconn->surface, "で") ||
     !strcmp(tcase->surface, "で")   )
   flags |= FG_HAS_DE;

 if (!strcmp(tconn->surface, "と") ||
     !strcmp(tcase->surface, "と")   )
   flags |= FG_HAS_TO;

 if (!strcmp(tconn->surface, "も") ||
     !strcmp(tcase->surface, "も")   )
   flags |= FG_HAS_MO;

 if (!strcmp(tconn->surface, "の") ||
     !strcmp(tcase->surface, "の")   )  // FIXME "連体化"みるべき
   flags |= FG_HAS_ADNOM_NO;

 if (c1 && !strcmp(c1, "並立助詞") ||
     a1 && !strcmp(a1, "並立助詞") ||
     hasTO() )           // 9/13/2012 「と」も並立助詞扱い（FIXME 正しいか？）
   flags |= FG_HAS_PARA;

 if (!strcmp(get_token(thead, 0), "感動詞")   ||
     !strcmp(get_token(thead, 0), "接続詞") &&
      ( cabch->token_size == 1 ||
        cabch->token_size == 2 && hasComma() ))
   flags |= FG_IS_SOLOCONJ_INTERJ;

  // Note: PREFER_NOUN/PRED are set in kakarotBuild()

#if 1
   if      (!strcmp(get_token(tconn, 0), "連体詞"))
     setPreferNoun();

   else if (!strcmp(get_token(tconn, 0), "副詞"))
     setPreferPred();

      // FIXME 副詞は一部の（形容的な）連体詞・副詞にもかかる、としたいが、
      // まず辞書に分類を入れる必要がある

   else if ( !strcmp(get_token(tconn, 0), "動詞")   ||
             !strcmp(get_token(tconn, 0), "形容詞") ||
             !strcmp(get_token(tconn, 0), "助動詞")   )  {

     if      (strstr(get_token(tconn, 5), "体言接続") ||
              strstr(get_token(tconn, 5), "基本形")   )
       setPreferNoun();

     else if (strstr(get_token(tconn, 5), "連用形") ||
              strstr(get_token(tconn, 5), "仮定形") || // FIXME? 助動詞のみ？
              strstr(get_token(tconn, 5), "連用ニ接続") || //助動詞「ず」のみ
              strstr(get_token(tconn, 5), "連用テ接続") )
       setPreferPred();

      // 連体形・連用形以外はありえないと仮定 FIXME? 大丈夫か？
   }

   else if (!strcmp(get_token(tconn, 0), "名詞"))
     setPreferPred();   // 助詞省略と仮定、格補語のつもり

   else if (!strcmp(get_token(tconn, 0), "助詞")) {
     const char* c1 = get_token(tconn, 1);
     const char* c2 = get_token(tconn, 2);

     if (strcmp(get_token(tconn, 1), "終助詞")) // 終助詞以外の助詞
       setPreferPred();
     if (!strcmp(get_token(tconn, 1), "連体化")) // 連体化の「の」
       setPreferNoun();
     if (!strcmp(c1, "格助詞") &&
         c2 && !strcmp(c2, "連語")) { // 格助詞,連語のケース。連体形のもの
       if (!strcmp(tconn->surface, "という") ||
           !strcmp(tconn->surface, "による") ||
           !strcmp(tconn->surface, "に従う")   )  // FIXME TBC まだある！
         setPreferNoun();
     }
   }
    // 接続詞（非ソロ）は当面述語にかかるとする　「|出したように、そして|」
   else if (!strcmp(get_token(tconn, 0), "接続詞")) {
       if (!isSoloConjInterj())
         setPreferPred();
   }
#endif
}

//******************************************
//  もろもろのデータ構造、関数等

int nodecnt;
Tree* g_tree; //どこからでも木を見るショートカット。よい子は真似しないように
chunkBitmapC dependable[MAXCHUNKS];  // 各文節(??深さ??)の、係り先候補の文節セット
chunkBitmapC nounChunks, predChunks; // 名詞/述語の文節セット
chunkBitmapC paraChunks; // 並立助詞の文節セット
chunkBitmapC commaChunks; // コンマを持つ文節セット

int nounDistAry[MAXCHUNKS];  // 文節が名詞だったら＋１されていく配列
int predDistAry[MAXCHUNKS];  // 文節が述語だったら＋１されていく配列
int commaLvlAry[MAXCHUNKS];  // コンマがあると＋１されていく配列

int nounDist(int s, int d) { // 文節間の「名詞距離」
 return (nounDistAry[d] - nounDistAry[s]);
}
int predDist(int s, int d) { // 文節間の「述語距離」
 return (predDistAry[d] - predDistAry[s]);
}
int commaLvl(int s, int d) { // 文節間の「コンマ距離」
 return (commaLvlAry[d] - commaLvlAry[s]);
}

//int findCase(Chunk*);  // 文節中の格辞を探す

int bestlinks[MAXCHUNKS][MAXCHUNKS];  // 最善の係り先の格納場所

int eval(); // defined below

void makedep(int s, int d) {
if (EDBG) printf("  makedep %d to %d\n", s, d);
 semChunks[s].dst = d;
 semChunks[d].srces[semChunks[d].nSrces++] = s;
 semChunks[s].hop = semChunks[d].hop + 1; 
}

void unmakedep(int s, int d) {
if (EDBG) printf("unmakedep %d to %d\n", s, d);
 semChunks[s].dst = -1;
   // FIXME 必ず最後に係ったsrcを外すと仮定している。正しいか？？
 assert(semChunks[d].srces[semChunks[d].nSrces - 1] == s);
 semChunks[d].srces[--semChunks[d].nSrces] = -1;
 semChunks[s].hop = -1; 
}

//******************************************
//  search()

 // search(nChunk-1, +Inf, mask(0)) で呼ぶ

int search(int d, int alpha, chunkBitmapC m) { // alphaはグローバルにする？
if (EDBG) printf("search entered d=%d A=%d m=%016llx\n", d, alpha, m.v);
 nodecnt++;
 int v = eval();
 if (d == -1) {
   if (EDBG) {
     printf("eval @ leaf. dst[]:\n");
     forr(k, 0, nChunk-1) {
       printf(" %d", semChunks[k].dst);
       if ((k%5)==4) printf(",");
     }
     printf("\n");
   }
   return v;
 }
 if (v >= alpha) return v;
 // assert(0<=d && d<nChunk);

  // dependable[d]の中をなめる
 chunkBitmapC cand = dependable[d] & ~m & chunkBitmapC::range(d+1,nChunk-1);
if (EDBG)
 printf("  dep=%016llx\n cand=%016llx\nm    =%016llx\nrange=%016llx\n",
       cand.v, dependable[d].v, m.v, chunkBitmapC::range(d+1,nChunk-1).v );

 if (cand.empty()) {  // FIXME tmp fix 係り先ないなら緊急避難で次の文節
   printf("WARNING: cand[%d] (%s) empty - set to next\n",
               d, g_tree->token(cabChunks[d]->token_pos)->surface);
   cand.set(d+1);
 }
 chunkItorC it(cand);
 for(; !it.atEnd(); ++it) {

   // d->jに係るとする
   int j = it.cur;

   //if (semChunks[j].nSrces == MAXSRC)
   //  continue;   // これ以上係れないのでスキップ
   assert(semChunks[j].nSrces < MAXSRC);

     // m2 = m | (d,j);   d-j間を係れなくする
   chunkBitmapC m2 = m;
   forr(i, d+1, j-1)
     m2.set(i);

    // 係りを進めて探索
   makedep(d,j);
   int vv = search(d-1, alpha, m2);
   unmakedep(d,j);
   if (vv < alpha) {
     alpha = vv;
     forr(k, 0, d-1)
       bestlinks[d][k] = bestlinks[d-1][k];
     bestlinks[d][d] = j;
     if (EDBG) {
        printf("bestlinks[%d]=%d upd v=%d 0-%d:\n", d, j, vv, d);
        forr(k, 0, d) {
          printf(" %d", bestlinks[d][k]);
          if ((k%5)==4) printf(",");
        }
        printf("\n");
     }
   }
 }
if (EDBG) printf("search returns v=%d\n", alpha);
 return alpha;
}

//******************************************
//  評価（コスト）関数用データ

#define MAXHOP 64
#define MAXGAWO 6
#define MAXNI   6
enum { COSTAB_ADNOM_NO = 0, COSTAB_HA = 1, COSTAB_NOUN = 2, COSTAB_PRED = 3,
       COSTAB_ANY = 4 };

#define TAKSAN44 \
 100, 110, 120, 130, 140,   150, 160, 170, 180, 190, \
 200, 210, 220, 230, 240,   250, 260, 270, 280, 290, \
 300, 310, 320, 330, 340,   350, 360, 370, 380, 390, \
 400, 410, 420, 430, 440,   450, 460, 470, 480, 490, \
 500, 510, 520, 530

enum { COST_AGAINST_RULE = 100, COST_OVER_COMMA = 36,
       COST_HA_TO_PRED2NOUN =  30, COST_FOLLOW_COMMA = 30,
       COST_NON_GA_TO_NONVERB = 8, COST_HA_NOTERM = 17,
       COST_HA_SEMITERM = 4

}; // FIXME tune

//#define USE_DSUF

#ifndef USE_DSUF
int distCostTable[5][MAXCHUNKS] = {  // FIXME tune
 {0,0, 7,10,13,  15,17,19,21, 23,   25, 27, 30, 38, 46,   53, 60, 68, 77, 87,
   TAKSAN44 },
 {0,0, 1, 2, 3,   4, 5, 7, 9, 11,   13, 15, 18, 21, 24,   33, 40, 48, 57, 57,
   TAKSAN44 },
 {0,0, 7,10,13,  15,17,19,21, 23,   25, 27, 30, 38, 46,   53, 60, 68, 77, 87,
   TAKSAN44 },
 {0,0, 2, 4, 6,   8,10,12,14, 17,   20, 24, 28, 34, 40,   50, 60, 68, 77, 87,
   TAKSAN44 },
 {0,0, 9,15,19,  24,28,32,36, 40,   44, 48, 50, 55, 59,   63, 67, 69, 77, 87,
   TAKSAN44 }
};
#else
enum { DSUF_NEXT = 0, DSUF_1 = 1, DSUF_2_8 = 2, DSUF_9PLUS = 3,DSUF_END=4};

int distCostTable[5][5] = {  // FIXME tune
 { 0, 0, 7, 13, 13 },  // NO
 { 0, 0, 2,  5,  4 },  // HA
 { 0, 0, 7, 13, 13 },  // NOUN
 { 0, 0, 2,  4,  4 },  // PRED
 { 0, 0, 9, 15, 15 }   // ANY
};
#endif


int nGaCostTable[MAXGAWO] = {  // FIXME tune
 0, 0, 22, 33, 44, 55
};
int nWoCostTable[MAXGAWO] = {  // FIXME tune
 0, 0, 22, 33, 44, 55
};
int nNiCostTable[MAXNI] = {    // FIXME tune
 0, 0,  8, 19, 31, 41
};

//******************************************
//  eval()    評価（コスト）関数

int eval() {
if (EDBG) printf("eval entered\n");
 int cost = 0;
 int hop = 0;

 forr(c, 0, nChunk-1) {   // 各文節について
   if (EDBGE) printf("---- eval: ch=%d\n", c);

   if (c < nChunk-2 && semChunks[c].dst >= 0) {
      // この文節*から*係るリンクのコスト。 最後２つは除く(共通)
     int s = c;
     int d = semChunks[s].dst;
     semChunkC& srcch = semChunks[s];
     semChunkC& dstch = semChunks[d];

     if (srcch.isSoloConjInterj()) continue;  // 接続詞・感動詞はスキップ

     /* ・ルール外接続は減点
     */
     bool prefN = srcch.preferNoun();
     bool prefP = srcch.preferPred();
     bool ruled = (prefN ? dstch.isNoun() :
                   prefP ? dstch.isPred() : true) ||
                   srcch.hasPara() && dstch.hasPara();
     if (!ruled) {
       cost += COST_AGAINST_RULE;
       if (EDBGE) printf("----==== norule: %d\n", COST_AGAINST_RULE);
     }

     /* ・dstへの距離   1/2-5/6- ?
     *     「名詞距離」「述語距離」を考慮
     * 　　距離１は基本ゼロコスト
     *     コンマ直後の距離１は減点（コストup）
     * 　　「は」格ならば緩和（コストdown） - 遠くても可（？）
     * 　　連体の「の」ならば遠いときのコストをup
     */
     int dtyp, dist;
     if (prefN && ruled) {
       dist = nounDist(s, d);
       //printf("dist noun: s=%d d=%d dist=%d\n", s, d, dist);
       dtyp = (srcch.hasAdnomNO() ? COSTAB_ADNOM_NO : COSTAB_NOUN);
     } else if (prefP && ruled) {
       dist = predDist(s, d);
       dtyp = (srcch.hasHA()      ? COSTAB_HA    : COSTAB_PRED);
     } else {
       dist = d - s;
       dtyp = COSTAB_ANY;
     }

#ifdef USE_DSUF
     int dsuf = (d - s == 1) ? DSUF_NEXT :
            (dist  == 1) ? DSUF_1    :
            dstch.hasTermination() ? DSUF_END    :
            (dist  >= 9) ? DSUF_9PLUS:
                           DSUF_2_8   ;
     cost += distCostTable[dtyp][dsuf];
     if (EDBGE) printf("----==== dist: %d\n", distCostTable[dtyp][dsuf]);
#else
     cost += distCostTable[dtyp][dist];
     if (EDBGE) printf("----==== dist: %d\n", distCostTable[dtyp][dist]);
#endif

     if (srcch.hasComma() && d-s==1) {
       cost += COST_FOLLOW_COMMA;  // コンマ直前から直後は減点
       if (EDBGE) printf("----==== follow comma: %d\n", COST_FOLLOW_COMMA);
     }

     if (!srcch.hasComma() && commaLvl(s, d) > 0) {
       cost += COST_OVER_COMMA; // コンマ無し文節からコンマ越えて係るのは減点
       if (EDBGE) printf("----==== over   comma: %d\n", COST_OVER_COMMA);
     }

     /* ・「は」格は連体節になる述語にはかからない（？正しいか？）
     * 　　主辞が動/形[動]/名+ダ で、
     * 　　接続辞が連体形(+ノ）で、
     * 　　srcの中に「は」格があれば減点
     */

     if (dstch.isPred2Noun() && srcch.hasHA()) {
       cost += COST_HA_TO_PRED2NOUN;
       if (EDBGE) printf("----==== pred2nown   : %d\n", COST_HA_TO_PRED2NOUN);
     }

     /* ・「は」格は「切れ目」になる述語にかかりやすい（？正しいか？）
     * 　　srcの中に「は」格があって
     * 　　dstが文末はOK、接続助詞＋コンマは次善、それ以外は減点
     */

     if (!dstch.hasTermination() && srcch.hasHA()) {
       int x = (dstch.hasPostpConn() && dstch.hasComma()) ? COST_HA_SEMITERM :
                                                            COST_HA_NOTERM ;
       cost += x;
       if (EDBGE) printf("----==== ha2term     : %d\n", x);
     }

     /* ・「が」格以外は動詞以外の述語にはかかりにくい
     * 　　動詞でない述語があって
     * 　　srcesの中に「は」格があれば減点
     */

     if (dstch.isPred() && !dstch.isVerb() && srcch.hasNonGACase()) {
       cost += COST_NON_GA_TO_NONVERB;
       if (EDBGE) printf("----==== nonga2noverb: %d\n", COST_NON_GA_TO_NONVERB);
     }

   }  // if この文節から係る

   // この文節*へ*係るリンクのコスト
   int d = c;
   semChunkC& dstch = semChunks[d];

     /* ・同じ格の補語が複数は減点
     * 　　自分が述語で、
     * 　　srcesの中にガ/ヲ/ニ/...格を数え、同じ格が複数あるなら減点
     *                                      （ニは２個許す？）
     */
   if (dstch.isPred()) {
     int nGa = 0, nWo = 0, nNi = 0;
     forr(s, 0, dstch.nSrces-1) {  // 係り元をなめる
       semChunkC& srcch = semChunks[dstch.srces[s]];
       if      (srcch.hasGA()) nGa++;
       else if (srcch.hasWO()) nWo++;
       else if (srcch.hasNI()) nNi++;
     }
     int x = nGaCostTable[std::min(nGa, MAXGAWO-1)] +
             nWoCostTable[std::min(nWo, MAXGAWO-1)] +
             nNiCostTable[std::min(nNi, MAXNI-1)];
     cost += x;
     if (EDBGE) printf("----==== gawoni      : %d\n", x);
   }

   assert(dstch.nSrces < MAXSRC);

   hop = std::max(hop, semChunks[c].hop);

   // 他に評価すべき項目あるか？？　TBC

 } // forr 各文節

if (EDBG) printf("eval returns v=%d\n", cost);
 return cost; 
}

//******************************************
//  kakarotOpen()    エンジン全体の初期化

void kakarotOpen(const Param& param) { // TBC 品詞〜係り先テーブル読み込み、等
  std::string dbgmode = param.get<std::string>("debug-mode");
  //std::cout << "modeopt: " << dbgmode << ";\n";

  // -g1 : debug mode   -g2 : compare-cabocha mode

  if (!strcmp(dbgmode.c_str(), "1"))
    EDBG = 1;
  if (!strcmp(dbgmode.c_str(), "2"))
    CMP_CABOCHA = 1;
}

//******************************************
//  kakarotBuild()    文章ごとの初期化

void kakarotBuild(Tree* tree) {
 g_tree = tree;  // デバッグ用どこでもドア

  // cabochaデータへのリンクをセット
 nChunk = tree->chunk_size();
 forr(i,0,nChunk-1)
   cabChunks[i] = tree->mutable_chunk(i);

  // semChunks[]初期化・セットアップ
 forr(i,0,nChunk-1)
   semChunks[i].build(tree);

  // 名詞文節・述語文節をリストアップ
 nounChunks.init();
 predChunks.init();
 paraChunks.init();
 commaChunks.init();
 int ndis = 0, pdis = 0, clvl = 0;

 forr(i,0,nChunk-1) {
   semChunkC& ch = semChunks[i];
   commaLvlAry[i] = clvl;
   if (ch.isNoun()) {
     ndis++;
     nounChunks.set(i);
   }
   if (ch.isPred()) {
     pdis++;
     predChunks.set(i);
   }
   if (ch.hasPara())
     paraChunks.set(i);
   if (ch.hasComma()) {
     clvl++;
     commaChunks.set(i);
   }

   nounDistAry[i] = ndis;
   predDistAry[i] = pdis;
   dependable[i].init();
 }

if (EDBG) printf("nCh: %016llx  pCh: %016llx\n", nounChunks.v, predChunks.v);

  // 係り文節候補を決める
 forr(i,0,nChunk-1) {
   semChunkC& ch = semChunks[i];

   //const Token* thead = tree->token(ch.buddy()->head_pos);
   //nst Token* tconn = tree->token(ch.buddy()->token_pos+ch.buddy()->func_pos);
   //const Token* tcase = tree->token(ch.caseTokenID);


   //if ( !strcmp(get_token(tconn, 0), "助詞") &&
   //     !strcmp(get_token(tconn, 1), "並立助詞"))
   if (ch.hasPara())
       dependable[i] |= paraChunks;  // 述語か並立助詞 FIXME これでいい?
           // 「XXとかYYとかがある」 XX->YY, YY->ある
    // 接続詞（非ソロ）は当面述語にかかるとする　「|出したように、そして|」
   else if (ch.isSoloConjInterj())
         dependable[i].set(i+1);


   if (ch.preferNoun())
       dependable[i] |= nounChunks;
   if (ch.preferPred())
       dependable[i] |= predChunks;

   if (i < nChunk-1 && dependable[i].empty()) {
       printf("WARNING: chunk[%d] (%s) has no candidate - set to next\n",
               i, tree->token(cabChunks[i]->token_pos)->surface);
       dependable[i].set(i+1);
   }
 }

if (EDBG) forr(i,0,nChunk-1)
  printf("cand[%2d]:%016llx\n", i, dependable[i].v);

  // 各種文節属性をダンプ
if (EDBG) {
#define NATTRS 26
 const char* lbl[NATTRS] = { 0,
  "PrefN", "PrefP", "isN  ", "isP  ", "hasNO",
  "hasHA", "hasGA", "hasWO", "hasNI", "Comma",
  "Para ", "ConIn", "P2N  ", "Term ", "LPar ",
  "RPar ", "LQuo ", "RQuo ", "hasTO", "hasDE",
  "hasMO", "isV  ", "PCon ", "PTerm", "Conj " 
 };
 forr(k,1,NATTRS-1) {
   printf("%s: ", lbl[k]);
   forr(i,0,nChunk-1) {
     printf("%d", ((1 << k) & semChunks[i].flags) ? 1 : 0);
     if ((i%5)==4) printf(" ");
   }
   printf("\n");
 }

 printf("distAry:\n");
 forr(k,0,nChunk-1) {
   printf("%d ", nounDistAry[k]);
   if ((k%5)==4) printf(" ");
 }
 printf("\n");
}

 // TBC...
}

//******************************************
//  kakarotParse()

#define INF (999999)

void kakarotParse(Tree* tree) {
 if (nChunk <= 0)
   return;

   // cabocha結果をセーブ
 forr(i,0,nChunk-1) {
   semChunks[i].cabLink = cabChunks[i]->link;
   semChunks[i].dst = -1;
 }

 semChunks[nChunk-1].dst = -1;  // 最後の文節は係り先なし
 bestlinks[nChunk-1][nChunk-1] =
 bestlinks[nChunk-2][nChunk-1] = -1;  // 最後の文節は係り先なし
 if (nChunk == 1) return;

  // 最後１つ手前の文節は必ず最後のに係る FIXME 倒置あると嘘！
 semChunks[nChunk-2].dst = nChunk-1;
 bestlinks[nChunk-2][nChunk-2] = nChunk-1;
 if (nChunk == 2) return;

 nodecnt = 0;
 search(nChunk-3, INF, chunkBitmapC(0LL));

if (CMP_CABOCHA) {
 printf("#### Parse ended. nodecnt=%d\n", nodecnt);

  // 出力結果比較
 int i;
 for(i=0; i<nChunk-2; i++)
   if (semChunks[i].cabLink != bestlinks[nChunk-3][i] &&
       !semChunks[i].isSoloConjInterj())
     break;
 if (i != nChunk-2) { // loop broken, i.e. unmatch
   printf("#### Parse Results Unmatched. i=%d\ncab:\n", i);
   forr(i, 0, nChunk-1)
     printf("%3d ", semChunks[i].cabLink);
   printf("\n");
   forr(i, 0, nChunk-3)
     printf("  %c ", (semChunks[i].cabLink!=bestlinks[nChunk-3][i]) ?
                      (semChunks[i].isSoloConjInterj() ? '-' : '*') : ' ');
   printf("\nkak:\n");
   forr(i, 0, nChunk-3)
     printf("%3d ", bestlinks[nChunk-3][i]);
   printf("%3d %3d\n", bestlinks[nChunk-2][nChunk-2]
                     , bestlinks[nChunk-2][nChunk-1]);
 } else
   printf("#### Parse Results Matched.\n");

}  // if (CMP_CABOCHA)

//#define OUT_SUM
#ifdef OUT_SUM
  // 文末の述語と、それに直接かかるハガオニ格を出力（なぜ？知らん…）
 printf("out_sum:\n");
 semChunkC& lastch = semChunks[nChunk-1];
 //forr(i, 0, lastch.nSrces-1) {
 forr(i, 0, nChunk-2) {
   if (bestlinks[nChunk-(i==nChunk-2 ? 2 : 3)][i] != nChunk-1)
     continue;
   semChunkC& ch = semChunks[i];
   Chunk* cabch = ch.buddy();
   const Token* tconn = tree->token(cabch->token_pos + cabch->func_pos);
   if (!strcmp(tconn->surface, "を") ||
       !strcmp(tconn->surface, "は") ||
       !strcmp(tconn->surface, "が") ||
       !strcmp(tconn->surface, "に")   ) {
      int tkStt = cabch->token_pos;
      int tkEnd = tkStt + cabch->token_size - 1;
      forr(j, tkStt, tkEnd)
        printf("%s", tree->token(j)->surface);
   }
 }
 Chunk* cabch = lastch.buddy();
 int tkStt = cabch->token_pos;
 int tkEnd = tkStt + cabch->token_size - 1;
 forr(j, tkStt, tkEnd)
   printf("%s", tree->token(j)->surface);
 printf("\n");
#endif

  // cabochaデータへkakarotの結果を書く
 if (!CMP_CABOCHA) {
   forr(i, 0, nChunk-3) {
     cabChunks[i]->link = bestlinks[nChunk-3][i];
     cabChunks[i]->score = 0;
   }
 }

}

} // namespace CaboCha
