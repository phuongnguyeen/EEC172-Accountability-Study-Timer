// Phuong Nguyen
// Kencha Vang

//*****************************************************************************
//
// Application Name     - Timer Count Capture
// Application Overview - This application showcases Timer's count capture
//                        feature to measure frequency of an external signal.
// Application Details  -
// http://processors.wiki.ti.com/index.php/CC32xx_Timer_Count_Capture_Application
// or
// docs\examples\CC32xx_Timer_Count_Capture_Application.pdf
//
//*****************************************************************************

//standard include
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include "stdlib.h"

#include "simplelink.h"

// Driverlib includes
#include "rom.h"
#include "rom_map.h"
#include "hw_timer.h"
#include "hw_types.h"
#include "hw_memmap.h"
#include "hw_ints.h"
#include "uart.h"
#include "interrupt.h"
#include "prcm.h"
#include "gpio.h"
#include "utils.h"
#include "timer.h"
#include "pin.h"
#include "systick.h"

// Common interface includes
#include "gpio_if.h"
#include "uart_if.h"
#include "i2c_if.h"
#include "oled_test.h"
#include "timer_if.h"
#include "Adafruit_SSD1351.h"
#include "Adafruit_GFX.h"

#include "pin_mux_config.h"

// Custom includes
#include "utils/network_utils.h"

#define APPLICATION_VERSION     "1.1.1"
#define APP_NAME                "Timer Count Capture"
#define TIMER_FREQ              80000000

//*****************************************************************************
//                 GLOBAL VARIABLES -- Start
//*****************************************************************************
static volatile unsigned long g_ulSysTickValue;
static volatile unsigned long g_ulIntClearVector;
volatile int systick_expired = 1;
volatile uint64_t systick_wrapped = 0;
volatile uint64_t ulsystick_delta_us = 0;
volatile int cnt = 0;

volatile unsigned long PIN61_intcount = 0;
volatile unsigned int PIN61_intflag = 0;

volatile int print = 0;
volatile int print_cnt = 0;
volatile uint64_t dataBuffer[24]; //put the data inside here
volatile uint64_t data[24];
volatile uint64_t start_counting_flag = 0;
unsigned long previous;
volatile int second_count = 0;
int second_2 = 0;
int msg_count = 0;
volatile char msg[7] = {'0', '0', '0', '0', '0', '0', '\0'};
volatile int loop = 0;
volatile int same = 0;
volatile int tap = 0;
volatile int first_press = 1;
volatile int delete = 1;
volatile int msg_cnt = 0;
char hchar[3] = {'0', '0', '\0'};
char mchar[3] = {'0', '0', '\0'};
char schar[3] = {'0', '0', '\0'};
int x[8] = {16, 28, 40, 52, 64, 76, 88, 100};
int y = 56;
unsigned int hchange = 0;
unsigned int mchange = 0;
unsigned int stop_timer = 0;
volatile unsigned long timerA1_cnt = 0;

//variables to put into aws
SlDateTime startTime;
SlDateTime endTime;
unsigned long duration;

char send_data[512];

static unsigned long g_ulSamples[2];
static unsigned long g_ulFreq;
const double temp = 1.0 / 80.0;

// Stores the pulse length
volatile uint32_t pulse = 0;
volatile uint32_t distance_cm = 0;
volatile int num_away = 0;
volatile int same_away = 0;
int first = 1;
unsigned int cfont = WHITE;
unsigned int cback = BLACK;
unsigned int font = BLACK;
unsigned int back = WHITE;
unsigned int time_mode = 0;
int num_break = 0;

// Tells the main code if a pulse is being read at the moment
volatile int echowait = 0;
char break_print[10] = {'b','r','e','a', 'k', ' ', 'm', 'o', 'd', 'e'};
char *study_print[10] = {'s','t','u','d', 'y', ' ', 'm', 'o', 'd', 'e'};

#if defined(ccs) || defined(gcc)
extern void (* const g_pfnVectors[])(void);
#endif
#if defined(ewarm)
extern uVectorEntry __vector_table;
#endif
//*****************************************************************************
//                 MACRO DEFINITIONS
//*****************************************************************************
#define APPLICATION_NAME      "SSL"
#define APPLICATION_VERSION   "SQ24"
#define SERVER_NAME           "a2u5fkz35rxq4o-ats.iot.us-east-1.amazonaws.com"
#define GOOGLE_DST_PORT       8443

#define POSTHEADER "POST /things/Final_Board/shadow HTTP/1.1\r\n"
#define HOSTHEADER "Host: a2u5fkz35rxq4o-ats.iot.us-east-1.amazonaws.com\r\n"
#define CHEADER "Connection: Keep-Alive\r\n"
#define CTHEADER "Content-Type: application/json; charset=utf-8\r\n"
#define CLHEADER1 "Content-Length: "
#define CLHEADER2 "\r\n\r\n"

#define UART_PRINT              Report
#define FOREVER                 1
#define CONSOLE                 UARTA0_BASE
#define FAILURE                 -1
#define SUCCESS                 0
#define RETERR_IF_TRUE(condition) {if(condition) return FAILURE;}
#define RET_IF_ERR(Func)          {int iRetVal = (Func); \
                                   if (SUCCESS != iRetVal) \
                                     return  iRetVal;}

// NTP Client Implementation
#define NTP_SERVER "pool.ntp.org"
#define NTP_PORT 123
#define NTP_EPOCH 2208988800UL

#define APP_NAME                "UART timer console"

#define SPI_IF_BIT_RATE  100000

// the cc3200's fixed clock frequency of 80 MHz
// note the use of ULL to indicate an unsigned long long constant
#define SYSCLKFREQ 80000000ULL

// macro to convert ticks to microseconds
#define TICKS_TO_US(ticks) \
    ((((ticks) / SYSCLKFREQ) * 1000000ULL) + \
    ((((ticks) % SYSCLKFREQ) * 1000000ULL) / SYSCLKFREQ))\

// systick reload value set to 40ms period
// (PERIOD_SEC) * (SYSCLKFREQ) = PERIOD_TICKS
#define SYSTICK_RELOAD_VAL 3200000UL

#define TIMER_INTERVAL_RELOAD   40035 /* =(255*157) */
#define DUTYCYCLE_GRANULARITY   157
#define I2C_ADDRESS_BH1750 0x23
#define CMD_START_CONVERSION 0x10

//*****************************************************************************
//                 GLOBAL VARIABLES -- End: df
//*****************************************************************************

typedef struct PinSetting {
    unsigned long port;
    unsigned int pin;
} PinSetting;

static PinSetting PIN61 = { .port = GPIOA0_BASE, .pin = 0x40}; //actually pin15

//*****************************************************************************
//                 function definitions
//*****************************************************************************

// Board Initializations
static void BoardInit(void);
static void SPIInit(void);

// Timers
static void TimerA1Init(void);
void TimerA1IntHandler(void);
void TimerReset(unsigned long base);

static inline void SysTickReset(void);
static void SysTickHandler(void);
static void SysTickInit(void);
void timerFunction(void);
void TIMERA0ISR();

// GPIO Interrupts
static void GPIOA0IntHandler(void);
void inputInt();
void GPIOIRInit();

// Logic functions to read remote and decode
void decode();
void readRemote(void);
void decodeChar(unsigned long output);
void sendMyMessage(void);

// Logic functions used to count down and display onto OLED
void updatePosition(char c, int x, int y, unsigned int FC, unsigned int BG);
void IntToASCII(unsigned long time, char* str);
void catInitString();
unsigned long ASCIItoInt(char* timestr);
void displayChar(void);
void Captureinit();
void InitConsole();

// Light Sensor

// Wifi
static void WifiInit(void);
static void PostDataToAWS(SlDateTime startTime, SlDateTime endTime, unsigned long ihours, unsigned long iminutes, unsigned long iseconds);
static int set_time();



//*****************************************************************************
//
//! Timer interrupt handler
//
//*****************************************************************************

void TimerDelayHandler()
{
    Timer_IF_InterruptClear(TIMERA1_BASE);
    echowait = 0; // Clear echowait flag after the delay
}

static void GPIOA0IntHandler(void){ // SW3 handler

    //get and clear status
    unsigned long ulStatus;

    ulStatus = MAP_GPIOIntStatus(PIN61.port, true);
    MAP_GPIOIntClear(PIN61.port, ulStatus);        // clear interrupts on GPIOA0

    //check if int occurred on pin61
    if (ulStatus & PIN61.pin){
        uint64_t current = SysTickValueGet();
        ulsystick_delta_us = TICKS_TO_US(SYSTICK_RELOAD_VAL - current); //calculates time difference
        PIN61_intflag = 1;
    }

    return;
}

static void SysTickHandler(void){
    systick_expired++;
    cnt++;
    second_count++;
        if(start_counting_flag == 1 && stop_timer == 0){
            if(second_count == 25){
            second_count = 0;
            seconds = seconds - 1;
            timerFunction();

        }
    }
}

void inputInt()
{
    // Clear interrupt flag. Since we only enabled one, this is enough
    MAP_GPIOIntClear(GPIOA2_BASE, PIN_08);

    /*
      If it's a rising edge then set the timer to 0
      It's in periodic mode so it was in some random value
    */
    if (GPIOPinRead(GPIOA2_BASE, PIN_08) == 2)
    {
        HWREG(TIMERA2_BASE + TIMER_O_TAV) = 0; // Loads value 0 into the timer.
        TimerEnable(TIMERA2_BASE, TIMER_A);
        echowait = 1;
    }
    /*
      If it's a falling edge that was detected, then get the value of the counter
    */
    else
    {
        pulse = TimerValueGet(TIMERA2_BASE, TIMER_A);
        TimerDisable(TIMERA2_BASE, TIMER_A);
        echowait = 0;
    }
}

void GPIOIRInit(){
    //
    // Register the interrupt handlers
    //
    MAP_GPIOIntRegister(PIN61.port, GPIOA0IntHandler);
    //
    // Configure rising edge interrupts on rising and falling edges
    //
    MAP_GPIOIntTypeSet(PIN61.port, PIN61.pin, GPIO_FALLING_EDGE);    // SW2

    uint64_t ulStatus = MAP_GPIOIntStatus (PIN61.port, false);
    MAP_GPIOIntClear(PIN61.port, ulStatus);            // clear interrupts

    // Enable interrupts
    MAP_GPIOIntEnable(PIN61.port, PIN61.pin);
}

//*****************************************************************************
//
//! The interrupt reset for the first timer interrupt.
//!
//! \param  None
//!
//! \return none
//
//*****************************************************************************

static inline void SysTickReset(void){
    HWREG(NVIC_ST_CURRENT) = 1;
    systick_expired = 0;
}

//*****************************************************************************
//
//! Board Initialization & Configuration
//!
//! \param  None
//!
//! \return None
//
//*****************************************************************************
void BoardInit(void)
{
/* In case of TI-RTOS vector table is initialize by OS itself */
#ifndef USE_TIRTOS
  //
  // Set vector table base
  //
#if defined(ccs) || defined(gcc)
    MAP_IntVTableBaseSet((unsigned long)&g_pfnVectors[0]);
#endif
#if defined(ewarm)
    MAP_IntVTableBaseSet((unsigned long)&__vector_table);
#endif
#endif
    //
    // Enable Processor
    //
    MAP_IntMasterEnable();
    MAP_IntEnable(FAULT_SYSTICK);

    PRCMCC3200MCUInit();
}

static void SPIInit(void){
   //
   // Enable the SPI module clock
   //
   MAP_PRCMPeripheralClkEnable(PRCM_GSPI,PRCM_RUN_MODE_CLK);
   MAP_PRCMPeripheralReset(PRCM_GSPI);
   //
   // Reset SPI
   //
   MAP_SPIReset(GSPI_BASE);

   //
   // Configure SPI interface
   //
   MAP_SPIConfigSetExpClk(GSPI_BASE,MAP_PRCMPeripheralClockGet(PRCM_GSPI),
                    SPI_IF_BIT_RATE,SPI_MODE_MASTER,SPI_SUB_MODE_0,
                    (SPI_SW_CTRL_CS |
                    SPI_4PIN_MODE |
                    SPI_TURBO_OFF |
                    SPI_CS_ACTIVEHIGH |
                    SPI_WL_8));

   //
   // Enable SPI for communication
   //
   MAP_SPIEnable(GSPI_BASE);

   Adafruit_Init();
   fillScreen(WHITE);

}

static void SysTickInit(void){

    //configure reset for systick
    MAP_SysTickPeriodSet(SYSTICK_RELOAD_VAL);

    //register interrupts on systick
    MAP_SysTickIntRegister(SysTickHandler);

    //enable interruptss on systick
    MAP_SysTickIntEnable();

    //enable systick module
    MAP_SysTickEnable();
}

static void WifiInit(void){
    long lRetVal = connectToAccessPoint();
    // initialize global default app configuration
    g_app_config.host = SERVER_NAME;
    g_app_config.port = GOOGLE_DST_PORT;

    //save the date and time int to slDateTime struct
    lRetVal = get_ntp_time(&startTime);

    if (lRetVal < 0) {  // Failed to get time from the NTP server
        return lRetVal;
    }
}

//*****************************************************************************
//
//!    spi display functions
//
//*****************************************************************************

//drawChar at the specified positions
void updatePosition(char c, int x, int y, unsigned int FC, unsigned int BG){
    drawChar(x, y, c, FC, BG, 2);
}

void IntToASCII(unsigned long time, char* str) {
    if (time >= 10) {
        str[0] = '0' + (time / 10); // Tens place
        str[1] = '0' + (time % 10); // Ones place
    } else {
        str[0] = '0';               // Tens place
        str[1] = '0' + time;        // Ones place
    }
    str[2] = '\0'; // Null-terminate the string
}

//print out the initial 00:00:00 string
void catInitString(){
    int i = 0;
    updatePosition(hchar[0], x[0], y, cfont, cback);
    updatePosition(hchar[1], x[1], y, font, back);
    updatePosition(':', x[2], y, font, back);
    for(i = 3; i < 5; i++) updatePosition(mchar[i-3], x[i], y, font, back);
    updatePosition(':', x[5], y, font, back);
    for(i = 6; i < 8; i++) updatePosition(schar[i-6], x[i], y, font, back);
}

//decode remote button pr4ess values
void decode(){
    int i;
    for(i = 0; i < 24; i++){
        out = (out << 1) | dataBuffer[i];
    }
}

void readRemote(){
    int i;
    if ((ulsystick_delta_us >= 7181) & (ulsystick_delta_us <= 8191)){ //Time difference between enable and end of signal bit
        PIN61_intcount = 0;
        memset(data, 0, sizeof(data));
        start = 1;
    } else if (start == 1){
        if ((ulsystick_delta_us >= 1024) & (ulsystick_delta_us <= 2100)){ //indicates 0
            data[PIN61_intcount] = 0;
            PIN61_intcount++;
        } else if (ulsystick_delta_us <= 5000){ // indicates 1
            data[PIN61_intcount] = 1;
            PIN61_intcount++;
        } else if (ulsystick_delta_us <= 8191){ //indicates repeated or held button
            PIN61_intcount = 0;
        } else if (ulsystick_delta_us <= 9215){ //end of signal
            count = cnt;
            if (count > 13) tap = 1; //initializes flag
            cnt = 0;
            PIN61_intcount = 0;
            int j = 0;
            for (j = 0; j < 23; j++) dataBuffer[j] = data[j]; //inputs data into another array that will be used to indicate button being pressed
            while (count > 0){
                print = 0;
                decode(); //figures out button input
                if (out == LAST){       // study mode
                    sendMyMessage();    // save the time
                    stop = 1;           // indicate that we are done reading signals and ready to start the timer
                    time_mode = 0;      //set mode flag
                    fillRect(0, 0, 128, 12, RED); // UI change to display that we are in study mode
                    for(i = 0; i < 10; i++){
                        drawChar(((128-(10*6))/2)+6*i , 2, study_print[i], WHITE, RED, 1);
                    }
                } else if (out == MUTE){    //break mode
                    sendMyMessage();
                    stop = 1;
                    time_mode = 1;          //set mode flag
                    num_break++;
                    fillRect(0, 0, 128, 12, BLUE);  // UI change to display that we are in break mode
                    for(i = 0; i < 10; i++){
                        drawChar(((128-(10*6))/2)+6*i , 2, break_print[i], WHITE, BLUE, 1);
                    }
                }
                else { //conditional statements for repeated button
                    if (first_press == 1){
                        first_press = 0;
                        decodeChar(out);
                    } else {
                        if (tap == 0){
                            loop++;
                        } else if (c != '\0') {     //reset char c
                            c = '\0';
                            msg_cnt++;
                            if(msg_cnt == 6){
                                msg_cnt = 0;
                            }
                        }
                        decodeChar(out);
                    }
                    if (c != '\0') displayChar();
                    if (msg_cnt == 5) {
                        fillRect(x[0], y, 12, 18, back);
                        updatePosition(msg[0], x[0], y, cfont, cback);
                    } else {    //mark the next position we want to edit with a different color
                        if(msg_cnt < 1){
                            fillRect(x[msg_cnt+1], y, 12, 16, back);
                            updatePosition(msg[msg_cnt+1], x[msg_cnt+1], y, cfont, cback);
                        } else if (msg_cnt >= 1 && msg_cnt < 3){
                            fillRect(x[msg_cnt+2], y, 12, 18, back);
                            updatePosition(msg[msg_cnt+1], x[msg_cnt+2], y, cfont, cback);
                        }
                        else {
                            fillRect(x[msg_cnt+3], y, 12, 18, back);
                            updatePosition(msg[msg_cnt+1], x[msg_cnt + 3], y, cfont, cback);
                        }
                    }
                    out = 0;
                    tap = 0;
                }
                count = 0;
            }
        }
    }
}

void decodeChar(unsigned long output){ //decode which character it is
    switch(output){
        case ZERO:
            c = '0';
            break;
        case ONE:
            c = '1';
            break;
        case TWO:
            c = '2';
            break;
        case THREE:
            c = '3';
            break;
        case FOUR:
            c = '4';
            break;
        case FIVE:
            c = '5';
            break;
        case SIX:
            c = '6';
            break;
        case SEVEN:
            c = '7';
            break;
        case EIGHT:
            c = '8';
            break;
        case NINE:
            c = '9';
            break;
        case LAST:
            //enter
            break;
        default:
            c = '\0';
            break;
    }

}

void sendMyMessage() {
    int i = 0;

    // Copy msg to hchar and print debug information
    for (i = 0; i < 2; i++) {
        if (msg[i] != '\0') {
            hchar[i] = msg[i];
        }
    }

    // Copy msg to mchar
    for (i = 2; i < 4; i++) {
        if (msg[i] != '\0') {
            mchar[i - 2] = msg[i];
        }
    }

    // Copy msg to schar
    for (i = 4; i < 6; i++) {
        if (msg[i] != '\0') {
            schar[i - 4] = msg[i];
        }
    }

    // Reset msg_cnt and convert ASCII to integer values
    msg_cnt = 0;
    hours = ASCIItoInt(hchar);
    minutes = ASCIItoInt(mchar);
    seconds = ASCIItoInt(schar);
}

unsigned long ASCIItoInt(char* timestr){
    unsigned long time;
    int i = 0;
    time = (timestr[0] - '0')*10;
    time = time + (timestr[1] - '0');
    return time;
}

void displayChar()
{
    msg[msg_cnt] = c;
    if (msg_cnt < 2){
        fillRect(x[msg_cnt], y, 12, 18, WHITE);
        updatePosition(c, x[msg_cnt], y, font, back);
    }
    else if (msg_cnt >= 2 && msg_cnt < 4){
        fillRect(x[msg_cnt+1], y, 12, 18, WHITE);
        updatePosition(c, x[msg_cnt + 1], y, font, back);
    }
    else if(msg_cnt >= 4 && msg_cnt < 6){
        fillRect(x[msg_cnt+2], y, 12, 18, WHITE);
        updatePosition(c, x[msg_cnt + 2], y, font, back);
    }
}

void timerFunction(){
    if(hchange == 1){
        hchange = 0;
        IntToASCII(hours, hchar);
        if(hours % 10 == 9) updatePosition(hchar[0], x[0], y, font, back);
        updatePosition(hchar[1], x[1], y, font, back);
    }
    if(mchange == 1){
        mchange = 0;
        IntToASCII(minutes, mchar);
        if(minutes % 10 == 9) updatePosition(mchar[0], x[3], y, font, back);
        updatePosition(mchar[1], x[4], y, font, back);
    }
    IntToASCII(seconds, schar);
    if(seconds % 10 == 9) updatePosition(schar[0], x[6], y, font, back);
    updatePosition(schar[1], x[7], y, font, back);

    if(seconds == 0){
        if(minutes == 0 && hours != 0){
            minutes = 60;
            hours = hours - 1;
            hchange = 1;
        } else if(minutes == 0 && hours == 0){
            stop_timer = 1;
        }
        seconds = 60;
        minutes = minutes - 1;
        mchange = 1;
    }
}

// Function to set the contrast for each color
void setContrast(unsigned char contrastA, unsigned char contrastB, unsigned char contrastC) {
    writeCommand(SSD1351_CMD_CONTRASTABC);
    writeData(contrastA);  // Red contrast
    writeData(contrastB);  // Green contrast
    writeData(contrastC);  // Blue contrast
}

// Function to set the overall brightness
void setBrightness(unsigned char brightness) {
    writeCommand(SSD1351_CMD_CONTRASTMASTER);
    writeData(brightness);  // Master contrast
}

// Function to adjust OLED brightness based on light intensity
void adjustOLEDbrightness(int lightIntensity) {
    int newBrightness = -1;
    if (lightIntensity >= 0 && lightIntensity <= 25) {
        newBrightness = 0;  // 0% Brightness
        setContrast(0x00, 0x00, 0x00);  // Lowest contrast
        setBrightness(0x00);            // Minimum brightness
    } else if (lightIntensity >= 26 && lightIntensity <= 60) {
        newBrightness = 25;  // 25% Brightness
        setContrast(0x40, 0x40, 0x40);  // Low contrast
        setBrightness(0x04);            // Low brightness
    } else if (lightIntensity >= 61 && lightIntensity <= 100) {
        newBrightness = 50;  // 50% Brightness
        setContrast(0x80, 0x80, 0x80);  // Medium contrast
        setBrightness(0x08);            // Medium brightness
    } else if (lightIntensity >= 101 && lightIntensity <= 160) {
        newBrightness = 75;  // 75% Brightness
        setContrast(0xC0, 0xC0, 0xC0);  // High contrast
        setBrightness(0x0C);            // High brightness
    } else if (lightIntensity >= 160) {
        newBrightness = 100;  // 100% Brightness
        setContrast(0xFF, 0xFF, 0xFF);  // Maximum contrast
        setBrightness(0x0F);            // Maximum brightness
    }
}

// Function to read light intensity from BH1750 sensor via I2C
uint16_t readLightIntensity() {
    uint8_t rxBuffer[2];
    uint16_t lux;

    // Read 2 bytes from the sensor
    I2C_IF_Read(I2C_ADDRESS_BH1750, rxBuffer, 2);

    // Convert the raw data to lux
    lux = (rxBuffer[0] << 8) | rxBuffer[1];
    lux /= 1.2;

    return lux;
}

// Timer ISR for handling periodic light intensity checks
void TIMERA0ISR() {
    int lightIntensity = readLightIntensity();
    adjustOLEDbrightness(lightIntensity);
    MAP_TimerIntClear(TIMERA0_BASE, TIMER_TIMA_TIMEOUT);  // Clear the timer interrupt
}
//*****************************************************************************
//
//!    aws and wifi functions
//
//*****************************************************************************
// Function to capture end time
void capture_start_time() {
    int lRetVal = get_ntp_time(&startTime);
}

// Function to capture end time
void capture_end_time() {
    int lRetVal = get_ntp_time(&endTime);
}

// Function to prepare and send data to AWS
void prepare_json_payload(char *buffer, size_t buffer_size) {
    snprintf(buffer, buffer_size,
             "{\"state\": {\"reported\": {"
             "\"device_id\": \"Final_Board\","
             "\"breaks\": 2,"
             "\"times_away\": %d,"
             "\"start_time\": \"%04d-%02d-%02d %02d:%02d:%02d\","
             "\"end_time\": \"%04d-%02d-%02d %02d:%02d:%02d\""
             "}}}",
             num_away, startTime.tm_year, startTime.tm_mon, startTime.tm_day,
             startTime.tm_hour, startTime.tm_min, startTime.tm_sec,
             endTime.tm_year, endTime.tm_mon, endTime.tm_day,
             endTime.tm_hour, endTime.tm_min, endTime.tm_sec);
}

//get time through NTP service
int get_ntp_time(SlDateTime *time) {
    int sock;
    struct sockaddr_in server_addr;
    unsigned char buffer[48] = {0};  // Combined request and response buffer
    int result;

    // Create socket
    sock = sl_Socket(SL_AF_INET, SL_SOCK_DGRAM, SL_IPPROTO_UDP);
    if (sock < 0) {
        return -1;
    }

    // Setup server address
    server_addr.sin_family = SL_AF_INET;
    server_addr.sin_port = sl_Htons(NTP_PORT);
    server_addr.sin_addr.s_addr = sl_Htonl(SL_IPV4_VAL(129, 6, 15, 28)); // NTP server IP

    // Send NTP request
    buffer[0] = 0x1B; // NTP request header
    result = sl_SendTo(sock, buffer, sizeof(buffer), 0, (SlSockAddr_t *)&server_addr, sizeof(server_addr));
    if (result < 0) {
        sl_Close(sock);
        return -1;
    }

    // Receive NTP response
    SlSocklen_t fromlen = sizeof(server_addr);
    result = sl_RecvFrom(sock, buffer, sizeof(buffer), 0, (SlSockAddr_t *)&server_addr, &fromlen);
    if (result < 0) {
        sl_Close(sock);
        return -1;
    }

    sl_Close(sock);

    // Extract time from response (seconds since 1900)
    unsigned long ntp_time = (buffer[40] << 24) | (buffer[41] << 16) | (buffer[42] << 8) | buffer[43];
    ntp_time -= NTP_EPOCH; // Convert to UNIX epoch

    // Convert to SlDateTime
    struct tm *tm_info = gmtime((time_t *)&ntp_time);
    if(tm_info->tm_hour >= 13){
        time->tm_hour = tm_info->tm_hour - 13;
        time->tm_day = tm_info->tm_mday - 1;
    } else {
        time->tm_hour = tm_info->tm_hour + 11;
        time->tm_day = tm_info->tm_mday - 2;
    }
    time->tm_mon = tm_info->tm_mon + 1;
    time->tm_year = tm_info->tm_year + 1970;
    time->tm_min = tm_info->tm_min;
    time->tm_sec = tm_info->tm_sec;

    return 0;
}

// Function to set time on device
static int set_time() {
    SlDateTime g_time;
    int lRetVal = get_ntp_time(&g_time);

    if (lRetVal < 0) {  // Failed to get time from NTP server
        return lRetVal;
    }

    lRetVal = sl_DevSet(SL_DEVICE_GENERAL_CONFIGURATION, SL_DEVICE_GENERAL_CONFIGURATION_DATE_TIME,
                        sizeof(SlDateTime), (unsigned char *)(&g_time));    //saved date and time into struct
    if (lRetVal < 0) {  // Unable to set time in the device
        return lRetVal;
    }

    return 0;
}

// Function to prepare and send data to AWS
static int http_post(int iTLSSockID) {
    char acSendBuff[1024];
    char acRecvbuff[1460];
    char cCLLength[200];
    char *pcBufHeaders;
    int lRetVal = 0;

    // Construct the HTTP POST request header
    pcBufHeaders = acSendBuff;
    strcpy(pcBufHeaders, POSTHEADER);
    pcBufHeaders += strlen(POSTHEADER);
    strcpy(pcBufHeaders, HOSTHEADER);
    pcBufHeaders += strlen(HOSTHEADER);
    strcpy(pcBufHeaders, CHEADER);
    pcBufHeaders += strlen(CHEADER);
    strcpy(pcBufHeaders, CTHEADER);
    pcBufHeaders += strlen(CTHEADER);

    // Prepare JSON payload
    char json_payload[512];
    prepare_json_payload(json_payload, sizeof(json_payload));
    int dataLength = strlen(json_payload);

    strcpy(pcBufHeaders, CLHEADER1);
    pcBufHeaders += strlen(CLHEADER1);
    sprintf(cCLLength, "%d", dataLength);
    strcpy(pcBufHeaders, cCLLength);
    pcBufHeaders += strlen(cCLLength);
    strcpy(pcBufHeaders, CLHEADER2);
    pcBufHeaders += strlen(CLHEADER2);

    // Add the JSON payload
    strcpy(pcBufHeaders, json_payload);
    pcBufHeaders += strlen(json_payload);

    // Send the packet to the server
    lRetVal = sl_Send(iTLSSockID, acSendBuff, strlen(acSendBuff), 0);
    if (lRetVal < 0) { //Post failed
        sl_Close(iTLSSockID);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }
    // Receive the response from the server
    lRetVal = sl_Recv(iTLSSockID, &acRecvbuff[0], sizeof(acRecvbuff), 0);
    if (lRetVal < 0) { // Recieved failed
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    } else {
        acRecvbuff[lRetVal + 1] = '\0';
    }

    return 0;
}

//*****************************************************************************
//
//! Main  Function
//
//*****************************************************************************
int main()
{
    //
    // Initialize Board configurations
    //
    BoardInit();

    //
    // Pinmux for UART
    //
    PinMuxConfig();

    SPIInit();
    SysTickInit();
    TimerA0Init();

    GPIOIRInit();


    // Initialize global default app configuration
    g_app_config.host = SERVER_NAME;
    g_app_config.port = GOOGLE_DST_PORT;

    // Connect the CC3200 to the local access point
    long lRetVal = connectToAccessPoint();

    // Set time so that encryption can be used
    lRetVal = set_time();
    if (lRetVal < 0) {  // Unable to set time in the device
        LOOP_FOREVER();
    }

    capture_start_time();

    WifiInit();
    catInitString();

    // collecting IR button presses until stop flag == 1
    while(!stop){
        while(PIN61_intflag){
            readRemote();
            PIN61_intflag = 0;
            SysTickReset();
        }
    }

    //save the initial study time in hours, minutes, and seconds
    unsigned long ihours = hours;
    unsigned long iminutes = minutes;
    unsigned long iseconds = seconds;

    //conversions for countdown time
    if(hours != 0 && minutes == 0){
        minutes = 60;
        hours = hours - 1;
        hchange = 1;
        mchange = 1;
    }
    if(minutes != 0 && seconds == 0){
        seconds = 60;
        minutes = minutes - 1;
        mchange = 1;
    }

    MAP_PRCMPeripheralClkEnable(PRCM_TIMERA2, PRCM_RUN_MODE_CLK);
    MAP_TimerConfigure(TIMERA2_BASE, TIMER_CFG_PERIODIC_UP);
    MAP_TimerEnable(TIMERA2_BASE, TIMER_A);


    // Initialize delay timer
    Timer_IF_Init(PRCM_TIMERA1, TIMERA1_BASE, TIMER_CFG_ONE_SHOT, TIMER_A, 0);
    Timer_IF_IntSetup(TIMERA1_BASE, TIMER_A, TimerDelayHandler);

    MAP_GPIOIntEnable(GPIOA2_BASE, PIN_08);
    MAP_GPIOIntTypeSet(GPIOA2_BASE, PIN_08, GPIO_BOTH_EDGES);
    MAP_TimerIntRegister(TIMERA2_BASE, TIMER_A, inputInt);
    MAP_GPIOIntRegister(GPIOA2_BASE, inputInt);
    InitPWMModules();

    second_2 = 0;
    second_count = 0;
    while (!stop_timer)
    {
        start_counting_flag = 1;
        // Collect 2 samples and compute the average
        const int num_samples = 2;
        uint32_t total_pulse = 0;
        int i;
        for (i = 0; i < num_samples; i++)
        {
            // Checks if a pulse read is in progress
            if (echowait != 1)
            {
                timerA1_cnt++;
                // Does the required pulse of 10uS
                MAP_GPIOPinWrite(GPIOA1_BASE, PIN_64, PIN_64);
                UtilsDelay(266);
                MAP_GPIOPinWrite(GPIOA1_BASE, PIN_64, ~PIN_64);

                echowait = 1; // Set echowait flag

                Timer_IF_Start(TIMERA1_BASE, TIMER_A, 10);

                // Wait until the delay is complete
                while (echowait != 0);

                // Convert the counter value to cm.
                pulse = (uint32_t)(temp * pulse);
                pulse = pulse / 58;

                total_pulse += pulse;
                if(time_mode == 0){
                if(pulse >= 55){
                    UpdateDutyCycle(TIMERA3_BASE, TIMER_B, 50); //turn buzzer on
                    if(same_away != 0){
                        same_away = 0;
                        num_away++;
                    }
                } else {
                   UpdateDutyCycle(TIMERA3_BASE, TIMER_B, 0);   //turn buzzer of
                    if(same_away != 1 || first == 1){
                        same_away = 1;
                        first = 0;
                    }
                }
                }
            }
        }

        // Compute average distance
        uint32_t average_pulse = total_pulse / num_samples;
    }
        // Prepare the JSON payload
        sprintf(send_data, "{\"state\":{\"reported\":{\"start_time\":{\"tm_sec\":%lu,\"tm_min\":%lu,\"tm_hour\":%lu,\"tm_day\":%lu,\"tm_mon\":%lu,\"tm_year\":%lu},\"end_time\":{\"tm_sec\":%lu,\"tm_min\":%lu,\"tm_hour\":%lu,\"tm_day\":%lu,\"tm_mon\":%lu,\"tm_year\":%lu},\"duration\":{\"hours\":%lu,\"minutes\":%lu,\"seconds\":%lu}}}}",
                startTime.tm_sec, startTime.tm_min, startTime.tm_hour,
                startTime.tm_day, startTime.tm_mon, startTime.tm_year,
                endTime.tm_sec, endTime.tm_min, endTime.tm_hour,
                endTime.tm_day, endTime.tm_mon, endTime.tm_year,
                ihours, iminutes, iseconds);

        lRetVal = set_time();
        if (lRetVal < 0) {  //Unable to set time in the device
            LOOP_FOREVER();
        }
        // Connect to the website with TLS encryption
        lRetVal = tls_connect();
        if (lRetVal < 0) {
            ERR_PRINT(lRetVal);
        }

        http_post(lRetVal);

        sl_Stop(SL_STOP_TIMEOUT);
        LOOP_FOREVER();
    capture_end_time();
    lRetVal = tls_connect();
    if (lRetVal < 0) {
        ERR_PRINT(lRetVal);
    }

    // Send data to AWS using the captured end time
    http_post(lRetVal);

    sl_Stop(SL_STOP_TIMEOUT);

    while(1){

    }
    return 0;
}
