/*
 * Viterbi.h 
 *
 *  Author: 
 *	 seobi,  2017-04-03  created 
 */ 
 
#ifndef __FEC_VITERBI__
#define __FEC_VITERBI__

#define CONSTRAINT_LEN_K			4
#define TMP_HDR_SIZE				0

#if CONSTRAINT_LEN_K == 5
#define PAD_SIZE 0
#else
#define PAD_SIZE 1
#endif

/*
	RF�� ���۵� FULL FRAME SIZE
*/
#define RF_FRAME_SIZE					106

/*
	RF�� ���۵� FRAME �� LAST BLOCK�� ������ ��� BLOCK�� BYTE SIZE
*/
#define	NBYTE_DIVISION					12
/*
	RF�� ���۵� FRAME �� LAST BLOCK �� BYTE SIZE
	LAST DIVISION�� 0�� ��� ����ó�� �ʿ�(�����Ƽ� ����)
*/
#define	NBYTE_LAST_DIVISION			(RF_FRAME_SIZE%NBYTE_DIVISION)

/*
	RF�� ���۵� FRAME �� LAST BLOCK�� ������ ��� BLOCK�� BIT SIZE
*/
#define N_BITS 							(NBYTE_DIVISION*8)
/*
	RF�� ���۵� FRAME �� LAST BLOCK BIT SIZE
*/
#define N_LAST_BITS 						(NBYTE_LAST_DIVISION*8)
/*
	RF�� ���۵� FRAME �� TOTAL BITS SIZE
*/
#define N_FULL_BITS						(RF_FRAME_SIZE*8)

/*
	RF�� ���۵�  SEGMENTED FRAME�� FEC FRAME SIZE 
*/
#define FEC_SYMBOL_LEN				(NBYTE_DIVISION*2)
/*
	RF�� ���۵� FULL FRAME �� FEC FRAME SIZE
*/
#define FEC_FULL_SYMBOL_LEN		(((((RF_FRAME_SIZE*8)+(CONSTRAINT_LEN_K-1))*2)>>3)+PAD_SIZE)



unsigned char *encode_first_fec(	unsigned char *data,   
										unsigned int nbytes );

unsigned char *encode_fec( unsigned char *data,   
								 unsigned int nbytes );	// 400 us

unsigned char *encode_last_fec( unsigned char *data,   
								 unsigned int nbytes );	// 44bytes: 160 us, 94bytes : 250 us

void decode_fec( 	unsigned char *data,	/* Decoded output data */	
						unsigned char *symbols  /* Raw deinterleaved input symbols */	 );

void decode_last_fec( 	unsigned char *data,	/* Decoded output data */	
						unsigned char *symbols /* Raw deinterleaved input symbols */	);

void Init_FEC(void);


void init_fec_decode( void );

#endif

