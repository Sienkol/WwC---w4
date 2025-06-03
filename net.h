//
#ifndef _NETWORK__H
#define _NETWORK__H

// VERSION FOR WINDOWS
#ifdef WIN32
//#include <ws2tcpip.h>       // odkomentowac gdy DEVCPP!!!
#else // VERSION FOR LINUX
#include <arpa/inet.h>  
#endif


class multicast_net
{
public:
	int sock;                         // Socket 

	struct sockaddr_in multicastAddr; // Multicast address 
	struct ip_mreq multicastRequest;  // Multicast address join strudture
	unsigned long multicastIP;             // IP Multicast address 
	unsigned short multicastPort;     // Server port 
	unsigned char multicastTTL;       // TTL of multicast packets

	unsigned char initS;
	unsigned char initR;

#ifdef WIN32
	WSADATA localWSA; //***************** for Windows
#endif

	multicast_net(char*, unsigned short);
	~multicast_net();

	int init_send();
	int init_recive();

	int send(char*, int);          // send data , size of data 
	int reciv(char*, int);          // recive  data , size of buffer to recive
};


class unicast_net
{
public:
	int sock;                         // Socket 
	struct sockaddr_in udpServAddr; // Local address 
	struct sockaddr_in udpClntAddr; // Client address 

	unsigned long udpIP;             // IP  address 
	unsigned short udpPort;     // Server port 

	short sSize;

#ifdef WIN32
	WSADATA localWSA; //***************** for Windows
#endif

	unicast_net(unsigned short); // port number
	~unicast_net();

	int send(char*, unsigned long, unsigned short); // pointer to data, IP Adres (unsigned long), size of data
	int reciv(char*, unsigned long *, unsigned short); // pointer to buffer,Sender IP Adres (unsigned long), size recive buffer

	int send(char*, char*, unsigned short); // pointer to data, IP Adres (string), size of data

};


#endif
