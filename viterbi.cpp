/*
 * viterbi.c  --  viterbi encoder/decoder + PRIMITIVE Interleaver
 *
 * Created: 2017-04-03 오후 8:34:15
 *  Author: seobi
 */ 

#include "viterbi.h"

#define PRIMITIVE_ROOT					31
#define FEC_PRIMITIVE_BIT_LEN			(NBYTE_DIVISION*8*2)


#if CONSTRAINT_LEN_K == 3 
#define	V27POLYA	0x07
#define	V27POLYB	0x05
#define FEC_PRIMITIVE_LAST_BIT_LEN		((NBYTE_LAST_DIVISION*8+(CONSTRAINT_LEN_K-1))*2)
#elif CONSTRAINT_LEN_K == 4
#define	V27POLYA	0x0F
#define	V27POLYB	0x0B
#define FEC_PRIMITIVE_LAST_BIT_LEN		((NBYTE_LAST_DIVISION*8+(CONSTRAINT_LEN_K-1))*2)
#elif CONSTRAINT_LEN_K == 5 //0x17, 0x19   |   0x13, 0x1b
#define	V27POLYA	0x13
#define	V27POLYB	0x1b
#define FEC_PRIMITIVE_LAST_BIT_LEN		((NBYTE_LAST_DIVISION*8+(CONSTRAINT_LEN_K-1))*2)
#else
#error not support CONSTRAINT_LEN_K
#endif


/* 
******************************************************************************* 
*			           constants and define declarations 
******************************************************************************* 
*/ 

typedef union { unsigned long w[2]; } decision_t;

unsigned int metric_array[2][2][(1<<(CONSTRAINT_LEN_K-2))];// ={{{0,15,8,8},{8,8,15,0}},{{8,8,0,15},{15,0,8,8}}};

 
/* State info for instance of Viterbi decoder
 */

struct viterbi_Info {
	decision_t *dp;              /* Pointer to decision output for current bit */
	unsigned int *old_metrics,*new_metrics,*temp_metrics; /* Pointers to path metrics, swapped on every bit */
	decision_t decisions[(N_FULL_BITS+(CONSTRAINT_LEN_K-1))];	  /* Beginning of decisions for block */
	unsigned int metrics1[1<<(CONSTRAINT_LEN_K-1)]; /* path metric buffer 1 */
	unsigned int metrics2[1<<(CONSTRAINT_LEN_K-1)]; /* path metric buffer 2 */
};


typedef struct _interleaver_info {
	unsigned int nInterleaver_byte_idx;
	unsigned int nInterleaver_bit_idx;
}interleaver_info;

interleaver_info g_interleaver_info[FEC_PRIMITIVE_BIT_LEN];
interleaver_info g_interleaver_last_info[FEC_PRIMITIVE_LAST_BIT_LEN];

/* 8-bit parity lookup table */   
unsigned int Partab[256];
int P_init = 0;
int g_chainback_cnt = 0;
int g_encstate = 0;
int	g_symbol_frame_idx = 0;
unsigned char symbol_frame_1[TMP_HDR_SIZE+FEC_SYMBOL_LEN];
unsigned char symbol_frame_2[TMP_HDR_SIZE+FEC_SYMBOL_LEN];
unsigned char symbol_frame_double[TMP_HDR_SIZE+(FEC_SYMBOL_LEN*2)];
struct viterbi_Info g_vInfo;
 

/* 
******************************************************************************* 
* 		                    local object definition 
******************************************************************************* 
*/ 
	
/* Create 256-entry odd-parity lookup table
* Needed only on non-ia32 machines
*/
static void partab_init(void){
	int i,cnt,ti;

	/* Initialize parity lookup table */
	for(i=0;i<256;i++){
		cnt = 0;
		ti = i;
		while(ti){
			if(ti & 1)
			cnt++;
			ti >>= 1;
		}
		
		Partab[i] = cnt & 1;
	}
	P_init=1;
}

static int parity(int x)
{
	if(!P_init)
		partab_init();

	/* Fold down to one byte */
	x ^= (x >> 16);
	x ^= (x >> 8);
	return Partab[x];
}

static void create_viterbi(void)
{
	struct viterbi_Info *vp = &g_vInfo;
	unsigned int Branchtab_1[(1<<(CONSTRAINT_LEN_K-2))];
	unsigned int Branchtab_2[(1<<(CONSTRAINT_LEN_K-2))];
	int state, i, j;

	/* Initialize metric tables */
	for(state=0;state < (1<<(CONSTRAINT_LEN_K-2));state++){
		Branchtab_1[state] = parity((2*state) & V27POLYA) ? 15:0;
		Branchtab_2[state] = parity((2*state) & V27POLYB) ? 15:0;
	}

	for(i=0;i<2;i++){
		for(j=0;j<2;j++){
			for(state=0;state < (1<<(CONSTRAINT_LEN_K-2));state++){
				metric_array[i][j][state] = ((Branchtab_1[state] ^ i*0x0F) + (Branchtab_2[state] ^ j*0x0F) + 1)>>1;
			}
		}
	}
	
	vp->dp = vp->decisions;
	vp->old_metrics = vp->metrics1;
	vp->new_metrics = vp->metrics2;
}


/* Do Viterbi chainback */
static inline void chainback_viterbi(
      unsigned char *data, /* Decoded output data */
      unsigned int nbits /* Number of data bits */ )
{ /* Terminal encoder state */
	register unsigned int k, n_frame_bit, n_frame_end_bit;
	decision_t *decisions = (decision_t *)(g_vInfo.decisions);
	unsigned int endstate = 0;

	/* Make room beyond the end of the encoder register so we can
	* accumulate a full byte of decoded data
	*/

	if( nbits != N_FULL_BITS ){
		g_chainback_cnt ++;
		if( g_chainback_cnt > 1 ){
			n_frame_bit = nbits * g_chainback_cnt;
			n_frame_end_bit = n_frame_bit - nbits - 8;
		}
		else{
			n_frame_bit = nbits;
			n_frame_end_bit = 0;
		}
	}else{
		n_frame_bit = nbits;
		n_frame_end_bit = n_frame_bit - N_LAST_BITS - 8;
	}
	
//	endstate %= (1<<(CONSTRAINT_LEN_K-1));
//	endstate <<= 2;
	decisions += (CONSTRAINT_LEN_K-1); /* Look past tail */

	while(n_frame_bit != n_frame_end_bit){
#if CONSTRAINT_LEN_K == 5
		/* The store into data[] only needs to be done every 8 bits.
		* But this avoids a conditional branch, and the writes will
		* combine in the cache anyway
		*/
		k = ((decisions[n_frame_bit-1].w[endstate >> 7] >> ((endstate >> 4)&15)) & 1);
		data[(n_frame_bit-1)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-2].w[endstate >> 7] >> ((endstate >> 4)&15)) & 1);
		data[(n_frame_bit-2)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-3].w[endstate >> 7] >> ((endstate >> 4)&15)) & 1);
		data[(n_frame_bit-3)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-4].w[endstate >> 7] >> ((endstate >> 4)&15)) & 1);
		data[(n_frame_bit-4)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-5].w[endstate >> 7] >> ((endstate >> 4)&15)) & 1);
		data[(n_frame_bit-5)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-6].w[endstate >> 7] >> ((endstate >> 4)&15)) & 1);
		data[(n_frame_bit-6)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-7].w[endstate >> 7] >> ((endstate >> 4)&15)) & 1);
		data[(n_frame_bit-7)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-8].w[endstate >> 7] >> ((endstate >> 4)&15)) & 1);
		data[(n_frame_bit-8)>>3] = endstate = (endstate >> 1) | (k<<7);

		n_frame_bit-=8;


#elif CONSTRAINT_LEN_K == 4
		/* The store into data[] only needs to be done every 8 bits.
		* But this avoids a conditional branch, and the writes will
		* combine in the cache anyway
		*/

		k = ((decisions[n_frame_bit-1].w[endstate >> 7] >> ((endstate >> 5)&7)) & 1);
		data[(n_frame_bit-1)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-2].w[endstate >> 7] >> ((endstate >> 5)&7)) & 1);
		data[(n_frame_bit-2)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-3].w[endstate >> 7] >> ((endstate >> 5)&7)) & 1);
		data[(n_frame_bit-3)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-4].w[endstate >> 7] >> ((endstate >> 5)&7)) & 1);
		data[(n_frame_bit-4)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-5].w[endstate >> 7] >> ((endstate >> 5)&7)) & 1);
		data[(n_frame_bit-5)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-6].w[endstate >> 7] >> ((endstate >> 5)&7)) & 1);
		data[(n_frame_bit-6)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-7].w[endstate >> 7] >> ((endstate >> 5)&7)) & 1);
		data[(n_frame_bit-7)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-8].w[endstate >> 7] >> ((endstate >> 5)&7)) & 1);
		data[(n_frame_bit-8)>>3] = endstate = (endstate >> 1) | (k<<7);
		
		n_frame_bit-=8;
#elif CONSTRAINT_LEN_K == 3
		/* The store into data[] only needs to be done every 8 bits.
		* But this avoids a conditional branch, and the writes will
		* combine in the cache anyway
		*/
		k = ((decisions[n_frame_bit-1].w[endstate >> 7] >> ((endstate >> 6)&3)) & 1);
		data[(n_frame_bit-1)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-2].w[endstate >> 7] >> ((endstate >> 6)&3)) & 1);
		data[(n_frame_bit-2)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-3].w[endstate >> 7] >> ((endstate >> 6)&3)) & 1);
		data[(n_frame_bit-3)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-4].w[endstate >> 7] >> ((endstate >> 6)&3)) & 1);
		data[(n_frame_bit-4)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-5].w[endstate >> 7] >> ((endstate >> 6)&3)) & 1);
		data[(n_frame_bit-5)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-6].w[endstate >> 7] >> ((endstate >> 6)&3)) & 1);
		data[(n_frame_bit-6)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-7].w[endstate >> 7] >> ((endstate >> 6)&3)) & 1);
		data[(n_frame_bit-7)>>3] = endstate = (endstate >> 1) | (k<<7);
		k = ((decisions[n_frame_bit-8].w[endstate >> 7] >> ((endstate >> 6)&3)) & 1);
		data[(n_frame_bit-8)>>3] = endstate = (endstate >> 1) | (k<<7);

		n_frame_bit-=8;
#else
#error not support CONSTRAINT_LEN_K
#endif
	}

	return;
}


//unsigned int g_sym1 = 0;
//unsigned int g_sym2 = 0;

/* C-language butterfly */
#if CONSTRAINT_LEN_K==5
#define BFLY0() \
	metric = metric_array[g_sym1][g_sym2][0];\
    m0 = g_vInfo.old_metrics[0] + metric;\
    m1 = g_vInfo.old_metrics[8] + (15 - metric);\
    decision1 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[0] = decision1 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision2 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[1] = decision2 ? m1 : m0;

#define BFLY1() \
	metric = metric_array[g_sym1][g_sym2][1];\
    m0 = g_vInfo.old_metrics[1] + metric;\
    m1 = g_vInfo.old_metrics[9] + (15 - metric);\
    decision3 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[2] = decision3 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision4 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[3] = decision4 ? m1 : m0;

#define BFLY2() \
	metric = metric_array[g_sym1][g_sym2][2];\
    m0 = g_vInfo.old_metrics[2] + metric;\
    m1 = g_vInfo.old_metrics[10] + (15 - metric);\
    decision5 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[4] = decision5 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision6 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[5] = decision6 ? m1 : m0;

#define BFLY3() \
	metric = metric_array[g_sym1][g_sym2][3];\
    m0 = g_vInfo.old_metrics[3] + metric;\
    m1 = g_vInfo.old_metrics[11] + (15 - metric);\
    decision7 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[6] = decision7 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision8 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[7] = decision8 ? m1 : m0;\
	g_vInfo.dp->w[0] = (decision1 | decision2 << 1 | decision3 << 2 | decision4 << 3 | decision5<<4 | decision6 << 5 | decision7 << 6 | decision8 << 7);

#define BFLY4() \
	metric = metric_array[g_sym1][g_sym2][4];\
    m0 = g_vInfo.old_metrics[4] + metric;\
    m1 = g_vInfo.old_metrics[12] + (15 - metric);\
    decision1 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[8] = decision1 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision2 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[9] = decision2 ? m1 : m0;

#define BFLY5() \
	metric = metric_array[g_sym1][g_sym2][5];\
    m0 = g_vInfo.old_metrics[5] + metric;\
    m1 = g_vInfo.old_metrics[13] + (15 - metric);\
    decision3 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[10] = decision3 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision4 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[11] = decision4 ? m1 : m0;

#define BFLY6() \
	metric = metric_array[g_sym1][g_sym2][6];\
    m0 = g_vInfo.old_metrics[6] + metric;\
    m1 = g_vInfo.old_metrics[14] + (15 - metric);\
    decision5 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[12] = decision5 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision6 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[13] = decision6 ? m1 : m0;

#define BFLY7() \
	metric = metric_array[g_sym1][g_sym2][7];\
    m0 = g_vInfo.old_metrics[7] + metric;\
    m1 = g_vInfo.old_metrics[15] + (15 - metric);\
    decision7 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[14] = decision7 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision8 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[15] = decision8 ? m1 : m0;\
	g_vInfo.dp->w[1] = (decision1<<8 | decision2 << 9 | decision3 << 10 | decision4 << 11 | decision5<<12 | decision6 << 13 | decision7 << 14 | decision8 << 15);


#define  update_viterbi() \
	BFLY0();\
	BFLY1();\
	BFLY2();\
	BFLY3();\
	BFLY4();\
	BFLY5();\
	BFLY6();\
	BFLY7();\
	if(g_vInfo.new_metrics[0] > 150){\
		unsigned char minmetric = 255;\
		for(k=0;k<(1<<(CONSTRAINT_LEN_K-1));k++)\
			if(g_vInfo.new_metrics[k] < minmetric)\
				minmetric = g_vInfo.new_metrics[k];\
		for(k=0;k<(1<<(CONSTRAINT_LEN_K-1));k++)\
			g_vInfo.new_metrics[k] -= minmetric;\
	}\
	g_vInfo.dp++;\
	g_vInfo.temp_metrics = g_vInfo.old_metrics;\
	g_vInfo.old_metrics = g_vInfo.new_metrics;\
	g_vInfo.new_metrics = g_vInfo.temp_metrics;

#elif CONSTRAINT_LEN_K == 4

#define BFLY0() \
	metric = metric_array[g_sym1][g_sym2][0];\
	m0 = g_vInfo.old_metrics[0] + metric;\
	m1 = g_vInfo.old_metrics[4] + 15 - metric;\
    decision1 = (m0-m1) >= 0;\
	g_vInfo.new_metrics[0] = decision1 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision2 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[1] = decision2 ? m1 : m0;

#define BFLY1() \
	metric = metric_array[g_sym1][g_sym2][1];\
	m0 = g_vInfo.old_metrics[1] + metric;\
	m1 = g_vInfo.old_metrics[5] + 15 - metric;\
    decision3 = (m0-m1) >= 0;\
	g_vInfo.new_metrics[2] = decision3 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision4 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[3] = decision4 ? m1 : m0;\
	g_vInfo.dp->w[0] = (decision1 | decision2 << 1 | decision3 << 2 | decision4 << 3);

#define BFLY2() \
	metric = metric_array[g_sym1][g_sym2][2];\
	m0 = g_vInfo.old_metrics[2] + metric;\
	m1 = g_vInfo.old_metrics[6] + 15 - metric;\
    decision1 = (m0-m1) >= 0;\
	g_vInfo.new_metrics[4] = decision1 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision2 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[5] = decision2 ? m1 : m0;

#define BFLY3() \
	metric = metric_array[g_sym1][g_sym2][3];\
	m0 = g_vInfo.old_metrics[3] + metric;\
	m1 = g_vInfo.old_metrics[7] + 15 - metric;\
    decision3 = (m0-m1) >= 0;\
	g_vInfo.new_metrics[6] = decision3 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision4 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[7] = decision4 ? m1 : m0;\
	g_vInfo.dp->w[1] = (decision1<<4 | decision2 << 5 | decision3 << 6 | decision4 << 7);

// update_viterbi : 2.62us
#define  update_viterbi() \
	BFLY0();\
	BFLY1();\
	BFLY2();\
	BFLY3();\
	if(g_vInfo.new_metrics[0] > 150){\
		unsigned char minmetric = 255;\
		for(k=0;k<8;k++)\
			if(g_vInfo.new_metrics[k] < minmetric)\
				minmetric = g_vInfo.new_metrics[k];\
		for(k=0;k<8;k++)\
			g_vInfo.new_metrics[k] -= minmetric;\
	}\
	g_vInfo.dp++;\
	g_vInfo.temp_metrics = g_vInfo.old_metrics;\
	g_vInfo.old_metrics = g_vInfo.new_metrics;\
	g_vInfo.new_metrics = g_vInfo.temp_metrics;

#elif CONSTRAINT_LEN_K == 3

#define BFLY0() \
	metric = metric_array[g_sym1][g_sym2][0];\
	m0 = g_vInfo.old_metrics[0] + metric;\
	m1 = g_vInfo.old_metrics[2] + (15 - metric);\
    decision1 = (m0-m1) >= 0;\
	g_vInfo.new_metrics[0] = decision1 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision2 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[1] = decision2 ? m1 : m0;\
	g_vInfo.dp->w[0] = (decision1 | decision2 << 1);

#define BFLY1() \
	metric = metric_array[g_sym1][g_sym2][1];\
	m0 = g_vInfo.old_metrics[1] + metric;\
	m1 = g_vInfo.old_metrics[3] + (15 - metric);\
    decision1 = (m0-m1) >= 0;\
	g_vInfo.new_metrics[2] = decision1 ? m1 : m0;\
    m0 -= (metric+metric-15);\
    m1 += (metric+metric-15);\
    decision2 = (m0-m1) >= 0;\
    g_vInfo.new_metrics[3] = decision2 ? m1 : m0;\
	g_vInfo.dp->w[1] = (decision1<<2 | decision2 << 3);


#define  update_viterbi() \
	BFLY0();\
	BFLY1();\
	if(g_vInfo.new_metrics[0] > 150){\
		unsigned char minmetric = 255;\
		for(k=0;k<4;k++)\
			if(g_vInfo.new_metrics[k] < minmetric)\
				minmetric = g_vInfo.new_metrics[k];\
		for(k=0;k<4;k++)\
			g_vInfo.new_metrics[k] -= minmetric;\
	}\
	g_vInfo.dp++;\
	g_vInfo.temp_metrics = g_vInfo.old_metrics;\
	g_vInfo.old_metrics = g_vInfo.new_metrics;\
	g_vInfo.new_metrics = g_vInfo.temp_metrics;

#else
#error not support CONSTRAINT_LEN_K
#endif


		



/* Initialize Viterbi decoder for start of new frame */
void init_fec_decode( void )
{
	register int i;
	for(i=0;i<1<<(CONSTRAINT_LEN_K-1);i++)
		g_vInfo.metrics1[i] = 60;

	g_vInfo.old_metrics = g_vInfo.metrics1;
	g_vInfo.new_metrics = g_vInfo.metrics2;
	g_vInfo.dp = g_vInfo.decisions;
	g_vInfo.old_metrics[0] = 0;
	g_chainback_cnt = 0;
}


/* 
*******************************************************************************  
* description: 
*	decode_fec : decoding main function + PRIMITIVE Interleaver + Data Chainback
* input:  
*	unsigned char *data : decoded data (OUT)
*	unsigned char *symbols : viterbi encoded symbols data (IN)
* output: 
*	none
*
*  12(24) :: 166us , 1/2 coderate, K=4
*
* function reference: 
* author: 
*	seobi,  2017-04-03	created 
******************************************************************************* 
*/ 
void decode_fec( 	unsigned char *data,	/* Decoded output data */	
						unsigned char *symbols  /* Raw deinterleaved input symbols */	 )
{
	register unsigned int g_sym1, g_sym2;
	register unsigned int metric;
#if CONSTRAINT_LEN_K == 4
	unsigned int decision1, decision2, decision3, decision4;
#elif CONSTRAINT_LEN_K == 3
	unsigned int decision1, decision2;
#else
	unsigned int decision1, decision2, decision3, decision4, decision5, decision6, decision7, decision8;
#endif
	int m0, m1;
	int k, i = 0;

	/* Decode block */
	do
	{
		g_sym1 = (symbols[g_interleaver_info[i].nInterleaver_byte_idx] & g_interleaver_info[i].nInterleaver_bit_idx) != 0; //  ? 15 : 0;
		g_sym2 = (symbols[g_interleaver_info[i+1].nInterleaver_byte_idx] & g_interleaver_info[i+1].nInterleaver_bit_idx) != 0; //  ? 15 : 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+2].nInterleaver_byte_idx] & g_interleaver_info[i+2].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+3].nInterleaver_byte_idx] & g_interleaver_info[i+3].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+4].nInterleaver_byte_idx] & g_interleaver_info[i+4].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+5].nInterleaver_byte_idx] & g_interleaver_info[i+5].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+6].nInterleaver_byte_idx] & g_interleaver_info[i+6].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+7].nInterleaver_byte_idx] & g_interleaver_info[i+7].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+8].nInterleaver_byte_idx] & g_interleaver_info[i+8].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+9].nInterleaver_byte_idx] & g_interleaver_info[i+9].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+10].nInterleaver_byte_idx] & g_interleaver_info[i+10].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+11].nInterleaver_byte_idx] & g_interleaver_info[i+11].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+12].nInterleaver_byte_idx] & g_interleaver_info[i+12].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+13].nInterleaver_byte_idx] & g_interleaver_info[i+13].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+14].nInterleaver_byte_idx] & g_interleaver_info[i+14].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+15].nInterleaver_byte_idx] & g_interleaver_info[i+15].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+16].nInterleaver_byte_idx] & g_interleaver_info[i+16].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+17].nInterleaver_byte_idx] & g_interleaver_info[i+17].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+18].nInterleaver_byte_idx] & g_interleaver_info[i+18].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+19].nInterleaver_byte_idx] & g_interleaver_info[i+19].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+20].nInterleaver_byte_idx] & g_interleaver_info[i+20].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+21].nInterleaver_byte_idx] & g_interleaver_info[i+21].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+22].nInterleaver_byte_idx] & g_interleaver_info[i+22].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+23].nInterleaver_byte_idx] & g_interleaver_info[i+23].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+24].nInterleaver_byte_idx] & g_interleaver_info[i+24].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+25].nInterleaver_byte_idx] & g_interleaver_info[i+25].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+26].nInterleaver_byte_idx] & g_interleaver_info[i+26].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+27].nInterleaver_byte_idx] & g_interleaver_info[i+27].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+28].nInterleaver_byte_idx] & g_interleaver_info[i+28].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+29].nInterleaver_byte_idx] & g_interleaver_info[i+29].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_info[i+30].nInterleaver_byte_idx] & g_interleaver_info[i+30].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_info[i+31].nInterleaver_byte_idx] & g_interleaver_info[i+31].nInterleaver_bit_idx) != 0;
		update_viterbi();

		i+=32;
	}while(i != FEC_DEC_BIT_LEN);

	/* Do Viterbi chainback */
	chainback_viterbi(data, N_BITS);
	return;
}

/* 
*******************************************************************************  
* description: 
*	decode_fec : decoding main function + PRIMITIVE Interleaver + Data Chainback
* input:  
*	unsigned char *data : decoded data (OUT)
*	unsigned char *symbols : viterbi encoded symbols data (IN)
* output: 
*	none
*
*  10(21) :: 160us, 1/2 coderate, K=4
*
* function reference: 
* author: 
*	seobi,  2017-04-03	created 
******************************************************************************* 
*/ 
void decode_last_fec( 	unsigned char *data,	/* Decoded output data */	
						unsigned char *symbols /* Raw deinterleaved input symbols */	)
{
	register unsigned int g_sym1, g_sym2;
	register unsigned int metric;
#if CONSTRAINT_LEN_K == 4
	unsigned int decision1, decision2, decision3, decision4;
#elif CONSTRAINT_LEN_K == 3
	unsigned int decision1, decision2;
#else
	unsigned int decision1, decision2, decision3, decision4, decision5, decision6, decision7, decision8;
#endif
	int m0, m1;
	int k, i = 0;

	/* Decode block */
	do{
		g_sym1 = (symbols[g_interleaver_last_info[i].nInterleaver_byte_idx] & g_interleaver_last_info[i].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+1].nInterleaver_byte_idx] & g_interleaver_last_info[i+1].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+2].nInterleaver_byte_idx] & g_interleaver_last_info[i+2].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+3].nInterleaver_byte_idx] & g_interleaver_last_info[i+3].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+4].nInterleaver_byte_idx] & g_interleaver_last_info[i+4].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+5].nInterleaver_byte_idx] & g_interleaver_last_info[i+5].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+6].nInterleaver_byte_idx] & g_interleaver_last_info[i+6].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+7].nInterleaver_byte_idx] & g_interleaver_last_info[i+7].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+8].nInterleaver_byte_idx] & g_interleaver_last_info[i+8].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+9].nInterleaver_byte_idx] & g_interleaver_last_info[i+9].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+10].nInterleaver_byte_idx] & g_interleaver_last_info[i+10].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+11].nInterleaver_byte_idx] & g_interleaver_last_info[i+11].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+12].nInterleaver_byte_idx] & g_interleaver_last_info[i+12].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+13].nInterleaver_byte_idx] & g_interleaver_last_info[i+13].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+14].nInterleaver_byte_idx] & g_interleaver_last_info[i+14].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+15].nInterleaver_byte_idx] & g_interleaver_last_info[i+15].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+16].nInterleaver_byte_idx] & g_interleaver_last_info[i+16].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+17].nInterleaver_byte_idx] & g_interleaver_last_info[i+17].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+18].nInterleaver_byte_idx] & g_interleaver_last_info[i+18].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+19].nInterleaver_byte_idx] & g_interleaver_last_info[i+19].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+20].nInterleaver_byte_idx] & g_interleaver_last_info[i+20].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+21].nInterleaver_byte_idx] & g_interleaver_last_info[i+21].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+22].nInterleaver_byte_idx] & g_interleaver_last_info[i+22].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+23].nInterleaver_byte_idx] & g_interleaver_last_info[i+23].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+24].nInterleaver_byte_idx] & g_interleaver_last_info[i+24].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+25].nInterleaver_byte_idx] & g_interleaver_last_info[i+25].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+26].nInterleaver_byte_idx] & g_interleaver_last_info[i+26].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+27].nInterleaver_byte_idx] & g_interleaver_last_info[i+27].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+28].nInterleaver_byte_idx] & g_interleaver_last_info[i+28].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+29].nInterleaver_byte_idx] & g_interleaver_last_info[i+29].nInterleaver_bit_idx) != 0;
		update_viterbi();

		g_sym1 = (symbols[g_interleaver_last_info[i+30].nInterleaver_byte_idx] & g_interleaver_last_info[i+30].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[i+31].nInterleaver_byte_idx] & g_interleaver_last_info[i+31].nInterleaver_bit_idx) != 0;
		update_viterbi();

		i+=32;
	}while(i != FEC_DEC_LAST_BIT_LEN);

#if CONSTRAINT_LEN_K == 4
	g_sym1 = (symbols[g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN].nInterleaver_byte_idx] & g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN].nInterleaver_bit_idx) != 0;
	g_sym2 = (symbols[g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+1].nInterleaver_byte_idx] & g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+1].nInterleaver_bit_idx) != 0;
	update_viterbi();

	g_sym1 = (symbols[g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+2].nInterleaver_byte_idx] & g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+2].nInterleaver_bit_idx) != 0;
	g_sym2 = (symbols[g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+3].nInterleaver_byte_idx] & g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+3].nInterleaver_bit_idx) != 0;
	update_viterbi();

	g_sym1 = (symbols[g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+4].nInterleaver_byte_idx] & g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+4].nInterleaver_bit_idx) != 0;
	g_sym2 = (symbols[g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+5].nInterleaver_byte_idx] & g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+5].nInterleaver_bit_idx) != 0;
	update_viterbi();
#else
	for(i=0;i<(CONSTRAINT_LEN_K-1)*2;i+=2){
		g_sym1 = (symbols[g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+i].nInterleaver_byte_idx] & g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+i].nInterleaver_bit_idx) != 0;
		g_sym2 = (symbols[g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+i+1].nInterleaver_byte_idx] & g_interleaver_last_info[FEC_DEC_LAST_BIT_LEN+i+1].nInterleaver_bit_idx) != 0;
		update_viterbi();
	}
#endif

	/* Do Viterbi chainback */
	chainback_viterbi(data, N_FULL_BITS);
	return;
}


/* 
*******************************************************************************  
* description: 
*	encode_first_fec : encoding main function + PRIMITIVE Interleaver
* input:  
*	unsigned char *data : original data frame (IN)
*	unsigned int nbytes : byte size of data frame (IN)
*
* output: 
*	unsigned char * : encoded viterbi frame (OUT)
*
* function reference: 
*
* 12bytes(24) : 25 us +  11us (SPI  interrupt setup time), 1/2 coderate, K=4
*
* author: 
*	seobi,  2017-04-03	created 
******************************************************************************* 
*/ 
unsigned char *encode_first_fec(	unsigned char *data,   
										unsigned int nbytes )
{
	register unsigned int sym_idx = 0;
	unsigned char *pSymbolPtr = &symbol_frame_double[TMP_HDR_SIZE];
	
	memset(symbol_frame_double, 0, sizeof(symbol_frame_double));
	g_encstate = 0;

	while(nbytes-- != 0){	
		g_encstate = (g_encstate << 1) | ((*data & 0x80) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+1].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+1].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x40) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+2].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+2].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+3].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+3].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x20) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+4].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+4].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+5].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+5].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x10) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+6].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+6].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+7].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+7].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x08) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+8].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+8].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+9].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+9].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x04) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+10].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+10].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+11].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+11].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x02) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+12].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+12].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+13].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+13].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x01) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+14].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+14].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+15].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+15].nInterleaver_bit_idx;

		sym_idx+=16;
		data++;   
	}

	return symbol_frame_double;
}



/* 
*******************************************************************************  
* description: 
*	encode_fec : encoding main function + PRIMITIVE Interleaver
* input:  
*	unsigned char *data : original data frame (IN)
*	unsigned int nbytes : byte size of data frame (IN)
*
* output: 
*	unsigned char * : encoded viterbi frame (OUT)
*
* function reference: 
*
* 12bytes(24) : 25 us +  11us (SPI  interrupt setup time), 1/2 coderate, K=4
*
* author: 
*	seobi,  2017-04-03	created 
******************************************************************************* 
*/ 
unsigned char *encode_fec(	unsigned char *data,   
								unsigned int nbytes )
{
	register int sym_idx = 0;
	unsigned char *pSymbolPtr;
	unsigned char *pRetPtr;

	if( !g_symbol_frame_idx ){
		g_symbol_frame_idx = 1;
		memset(symbol_frame_1, 0, sizeof(symbol_frame_1));
		pSymbolPtr = &symbol_frame_1[TMP_HDR_SIZE];
		pRetPtr = symbol_frame_1;
	}else{
		g_symbol_frame_idx = 0;
		memset(symbol_frame_2, 0, sizeof(symbol_frame_2));
		pSymbolPtr = &symbol_frame_2[TMP_HDR_SIZE];
		pRetPtr = symbol_frame_2;
	}

	while(nbytes-- != 0){	
		g_encstate = (g_encstate << 1) | ((*data & 0x80) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+1].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+1].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x40) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+2].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+2].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+3].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+3].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x20) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+4].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+4].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+5].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+5].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x10) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+6].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+6].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+7].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+7].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x08) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+8].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+8].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+9].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+9].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x04) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+10].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+10].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+11].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+11].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x02) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+12].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+12].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+13].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+13].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x01) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_info[sym_idx+14].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+14].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_info[sym_idx+15].nInterleaver_byte_idx] |= g_interleaver_info[sym_idx+15].nInterleaver_bit_idx;

		sym_idx+=16;
		data++;   
	}

	return pRetPtr;
}



/* 
*******************************************************************************  
* description: 
*	encode_fec : encoding main function + PRIMITIVE Interleaver
* input:  
*	unsigned char *data : original data frame (IN)
*	unsigned int nbytes : byte size of data frame (IN)
*
* output: 
*	unsigned char * : encoded viterbi frame (OUT)
*
* function reference: 
*
* 12bytes(24) : 25 us, 1/2 coderate, K=4
*
* author: 
*	seobi,  2017-04-03	created 
******************************************************************************* 
*/ 
unsigned char *encode_last_fec( 	unsigned char *data,   
										unsigned int nbytes )
{
	register int sym_idx = 0, endstate = 0;
	unsigned char *pSymbolPtr = &symbol_frame_double[TMP_HDR_SIZE];

	memset(symbol_frame_double, 0, sizeof(symbol_frame_double));

	while(nbytes-- != 0){	
		g_encstate = (g_encstate << 1) | ((*data & 0x80) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_last_info[sym_idx].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+1].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+1].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x40) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+2].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+2].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+3].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+3].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x20) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+4].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+4].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+5].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+5].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x10) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+6].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+6].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+7].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+7].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x08) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+8].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+8].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+9].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+9].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x04) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+10].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+10].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+11].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+11].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x02) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+12].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+12].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+13].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+13].nInterleaver_bit_idx;

		g_encstate = (g_encstate << 1) | ((*data & 0x01) != 0 );  
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+14].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+14].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+15].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+15].nInterleaver_bit_idx;

		sym_idx+=16;
		data++;   
	}

	/* Flush out tail */  
#if CONSTRAINT_LEN_K == 4
	g_encstate = (g_encstate << 1) | ((endstate & 0x04) != 0 );   
	if( Partab[g_encstate & V27POLYA] )
		pSymbolPtr[g_interleaver_last_info[sym_idx].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx].nInterleaver_bit_idx;

	if( Partab[g_encstate & V27POLYB] )
		pSymbolPtr[g_interleaver_last_info[sym_idx+1].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+1].nInterleaver_bit_idx;

	g_encstate = (g_encstate << 1) | ((endstate & 0x02) != 0 );   
	if( Partab[g_encstate & V27POLYA] )
		pSymbolPtr[g_interleaver_last_info[sym_idx+2].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+2].nInterleaver_bit_idx;

	if( Partab[g_encstate & V27POLYB] )
		pSymbolPtr[g_interleaver_last_info[sym_idx+3].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+3].nInterleaver_bit_idx;

	g_encstate = (g_encstate << 1) | ((endstate & 0x01) != 0 );   
	if( Partab[g_encstate & V27POLYA] )
		pSymbolPtr[g_interleaver_last_info[sym_idx+4].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+4].nInterleaver_bit_idx;

	if( Partab[g_encstate & V27POLYB] )
		pSymbolPtr[g_interleaver_last_info[sym_idx+5].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+5].nInterleaver_bit_idx;
#else
	for(int i=CONSTRAINT_LEN_K-2;i>=0;i--){   
		g_encstate = (g_encstate << 1) | ((endstate >> i) & 1);   
		if( Partab[g_encstate & V27POLYA] )
			pSymbolPtr[g_interleaver_last_info[sym_idx].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx].nInterleaver_bit_idx;

		if( Partab[g_encstate & V27POLYB] )
			pSymbolPtr[g_interleaver_last_info[sym_idx+1].nInterleaver_byte_idx] |= g_interleaver_last_info[sym_idx+1].nInterleaver_bit_idx;
		
		sym_idx+=2;
	}
#endif

	return symbol_frame_double;
}




   


//#define INTERLEAVER_DEBUG

#ifdef INTERLEAVER_DEBUG
short g_check[FEC_PRIMITIVE_BIT_LEN];  // 1510 (94기준)
short g_Interleaver[FEC_PRIMITIVE_BIT_LEN];  // 192 (12기준)
short g_Interleaver_last[FEC_PRIMITIVE_LAST_BIT_LEN];  // 166 (10기준)
#endif

static void init_primitive_interleaver( void )
{
	int   position = 0, i; 	
	int g_BitIndex[8] = {0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80};
	
#ifdef INTERLEAVER_DEBUG
	g_Interleaver[0] = 0;
#endif
	g_interleaver_info[0].nInterleaver_byte_idx = 0;
	g_interleaver_info[0].nInterleaver_bit_idx = g_BitIndex[0];

	for (i=1; i<FEC_PRIMITIVE_BIT_LEN; i++)   
	{	
		position = (position + PRIMITIVE_ROOT) % FEC_PRIMITIVE_BIT_LEN; 
		g_interleaver_info[i].nInterleaver_byte_idx = position>>3;
		g_interleaver_info[i].nInterleaver_bit_idx = g_BitIndex[position&7];
#ifdef INTERLEAVER_DEBUG
		g_Interleaver[i] = position;	 
#endif
	}	 
	
#ifdef INTERLEAVER_DEBUG
	memset(g_check, 0, sizeof(g_check));

	for (i=0; i<FEC_PRIMITIVE_BIT_LEN; i++) 
		g_check[g_Interleaver[i]] = 1;	

	for (i=0; i<FEC_PRIMITIVE_BIT_LEN; i++){
		if (!g_check[i]) {	
			while(1){
				printf("This is not a valid interleaver!\n");
			}
		}  
	}

	for (i=0; i<FEC_PRIMITIVE_BIT_LEN; i++)  
	{  
		printf("%5d -> %5d\n",i,g_Interleaver[i]);
	}  
#endif
	
}

static void init_primitive_last_interleaver( void )
{
	int   position = 0, i; 
	int g_BitIndex[8] = {0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80};
	
#ifdef INTERLEAVER_DEBUG
	g_Interleaver_last[0] = 0;
#endif
	g_interleaver_last_info[0].nInterleaver_byte_idx = 0;
	g_interleaver_last_info[0].nInterleaver_bit_idx = g_BitIndex[0];

	for (i=1; i<FEC_PRIMITIVE_LAST_BIT_LEN; i++)   
	{   
		position = (position + PRIMITIVE_ROOT) % FEC_PRIMITIVE_LAST_BIT_LEN;	
		g_interleaver_last_info[i].nInterleaver_byte_idx = position>>3;
		g_interleaver_last_info[i].nInterleaver_bit_idx = g_BitIndex[position&7];
#ifdef INTERLEAVER_DEBUG
		g_Interleaver_last[i] = position;	 
#endif
	}    
	
#ifdef INTERLEAVER_DEBUG
	memset(g_check, 0, sizeof(g_check));

	for (i=0; i<FEC_PRIMITIVE_LAST_BIT_LEN; i++) 
		g_check[g_Interleaver_last[i]] = 1;	

	for (i=0; i<FEC_PRIMITIVE_LAST_BIT_LEN; i++){
		if (!g_check[i]) {	
			while(1){
				printf("This is not a valid interleaver!\n");
			}
		}  
	}

	for (i=0; i<FEC_PRIMITIVE_LAST_BIT_LEN; i++)  
	{  
		printf("%5d -> %5d\n",i,g_Interleaver_last[i]);
	}  
#endif
	
}

  
/*
*/
void Init_FEC(void)
{
	init_primitive_interleaver();
	init_primitive_last_interleaver();
	partab_init();
	create_viterbi();
	init_fec_decode();
}



