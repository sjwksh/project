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
	RF로 전송될 FULL FRAME SIZE
*/
#define RF_FRAME_SIZE					106

/*
	RF로 전송될 FRAME 의 LAST BLOCK을 제외한 모든 BLOCK의 BYTE SIZE
*/
#define	NBYTE_DIVISION					12
/*
	RF로 전송될 FRAME 의 LAST BLOCK 의 BYTE SIZE
	LAST DIVISION이 0일 경우 예외처리 필요(귀찮아서 안함)
*/
#define	NBYTE_LAST_DIVISION			(RF_FRAME_SIZE%NBYTE_DIVISION)

/*
	RF로 전송될 FRAME 의 LAST BLOCK을 제외한 모든 BLOCK의 BIT SIZE
*/
#define N_BITS 							(NBYTE_DIVISION*8)
/*
	RF로 전송될 FRAME 의 LAST BLOCK BIT SIZE
*/
#define N_LAST_BITS 						(NBYTE_LAST_DIVISION*8)

/*
	RF로 전송될 FRAME 의 TOTAL BITS SIZE
*/
#define N_FULL_BITS						(RF_FRAME_SIZE*8)

/* 
	RF로 수신된 FEC FRAME 의 BITS SIZE
*/
#define FEC_DEC_BIT_LEN     (N_BITS*2) //12*8*2

/* 
	RF로 수신된 FEC FRAME 의 LAST BLOCK BITS SIZE
*/
#define FEC_DEC_LAST_BIT_LEN   (N_LAST_BITS*2) //10*8*2

/*
	RF로 전송될  SEGMENTED FRAME의 FEC FRAME SIZE 
*/
#define FEC_SYMBOL_LEN				(NBYTE_DIVISION*2)
/*
	RF로 전송될 FULL FRAME 의 FEC FRAME SIZE
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

