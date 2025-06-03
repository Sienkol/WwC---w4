/************************************************************
	Obs³uga sieci - multicast, unicast
	*************************************************************/

//#include <windows.h>
#include <stdio.h>      /* for printf() and fprintf() */
#include <stdlib.h>     /* for atoi() and exit() */
#include <string.h>     /* for memset() */
#include <time.h>
//#include <unistd.h>     /* for close() */

#ifdef WIN32// VERSION FOR WINDOWS
//#include <ws2tcpip.h>
//#include <winsock.h>
#include <winsock2.h>
#include <ws2tcpip.h>
#else // VERSION FOR LINUX
#include <sys/socket.h> /* for socket(), connect(), sendto(), and recvfrom() */
#include <arpa/inet.h>  /* for sockaddr_in and inet_addr() */
#endif


#include "net.h"

extern FILE *f;

HANDLE threadSend;


void DieWithError(char *errorMessage)
{
	perror(errorMessage);
	//exit(1);
}


multicast_net::multicast_net(char* ipAdress, unsigned short port)
{

#ifdef WIN32
	if (WSAStartup(MAKEWORD(2, 2), &localWSA) != 0)
	{
		printf("WSAStartup error.");
	}
#endif
	// wpisanie adresu i portu (zgodne ju¿ z formatem)
	multicastIP = inet_addr(ipAdress);
	multicastPort = htons(port);
	multicastTTL = 1;

	if ((sock = socket(PF_INET, SOCK_DGRAM, IPPROTO_UDP)) < 0)
		DieWithError("Socket() failed.");

	initS = 0;
	initR = 0;
	printf("Socket ok.\n");
}

multicast_net::~multicast_net()
{
	//close(sock);
#ifdef WIN32
	WSACleanup(); // ********************* For Windows
#endif

}

int multicast_net::init_recive()
{
	int on = 1;
	fprintf(stderr, "init receiver ");
	setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, (char *)&on, sizeof(on));

	if (!initS)
	{
		memset(&multicastAddr, 0, sizeof(multicastAddr));
		multicastAddr.sin_family = AF_INET;
		multicastAddr.sin_addr.s_addr = htonl(INADDR_ANY);
		multicastAddr.sin_port = multicastPort;

		// Bind to the multicast port 
		if (bind(sock, (struct sockaddr *) &multicastAddr, sizeof(multicastAddr)) < 0)
			DieWithError("bind() failed");
	}

	// Specify the multicast group 
	multicastRequest.imr_multiaddr.s_addr = multicastIP;
	// Accept multicast from any interface 
	multicastRequest.imr_interface.s_addr = htonl(INADDR_ANY);
	// Join the multicast address 
	if (setsockopt(sock, IPPROTO_IP, IP_ADD_MEMBERSHIP, (char *)&multicastRequest,
		sizeof(multicastRequest)) < 0)
		DieWithError("setsockopt() failed");
	//if (setsockopt(rsock, IPPROTO_IP, IP_ADD_MEMBERSHIP, (char *)&mreq, sizeof (mreq)) != 0)
	fprintf(stderr, " ok\n");
	initR = 1;
	return 1;

}

int multicast_net::init_send()
{
	fprintf(stderr, "init sender");

	// Set TTL of multicast packet 
	if (setsockopt(sock, IPPROTO_IP, IP_MULTICAST_TTL, (char *)&multicastTTL,
		sizeof(multicastTTL)) < 0)
		DieWithError("setsockopt() failed");


	// Construct local address structure 
	memset(&multicastAddr, 0, sizeof(multicastAddr));
	multicastAddr.sin_family = AF_INET;
	multicastAddr.sin_addr.s_addr = multicastIP;
	multicastAddr.sin_port = multicastPort;

	fprintf(stderr, " ok\n");

	initS = 1;


	return 1;

}

int multicast_net::send(char* buffer, int size)
{
	int sendsize;
	if (!initS) init_send();

	if ((sendsize = sendto(sock, buffer, size, 0, (struct sockaddr *)
		&multicastAddr, sizeof(multicastAddr))) != size)
		DieWithError("sendto() sent a different number of bytes than expected");

	return sendsize;
}


int multicast_net::reciv(char* buffer, int maxsize)
{
	int recvLen;

	if (!initR) init_recive();


	if ((recvLen = recvfrom(sock, buffer, maxsize, 0, NULL, 0)) < 0)    DieWithError("recvfrom() failed");

	return recvLen;

}
// #########################################
// ##############   UNICAST  ###############
// #########################################

unicast_net::unicast_net(unsigned short usPort)
{
	printf("UDP socket ");
#ifdef WIN32
	if (WSAStartup(MAKEWORD(2, 2), &localWSA) != 0)
	{
		printf("WSAStartup error");
	}
#endif
	/* Create a datagram/UDP socket */
	if ((sock = socket(PF_INET, SOCK_DGRAM, IPPROTO_UDP)) < 0)
		DieWithError("socket() failed");

	memset(&udpServAddr, 0, sizeof(udpServAddr));   /* Zero out structure */
	udpServAddr.sin_family = AF_INET;                /* Internet address family */
	udpServAddr.sin_addr.s_addr = htonl(INADDR_ANY); /* Any incoming interface */
	udpServAddr.sin_port = usPort;      /* Local port */

	if (bind(sock, (struct sockaddr *) &udpServAddr, sizeof(udpServAddr)) < 0)
		DieWithError("bind() failed");
	printf("OK\n");
}

unicast_net::~unicast_net()
{
	//close(sock);
#ifdef WIN32
	WSACleanup(); // ********************* For Windows
#endif
}


int unicast_net::send(char *buffer, char *servIP, unsigned short size)
{
	udpServAddr.sin_addr.s_addr = inet_addr(servIP);

	if (sendto(sock, buffer, size, 0, (struct sockaddr *)
		&udpServAddr, sizeof(udpServAddr)) == size) return size;
	else DieWithError("sendto() sent a different number of bytes than expected");
}

int unicast_net::send(char *buffer, unsigned long servIP, unsigned short size)
{
	udpServAddr.sin_addr.s_addr = servIP;

	if (sendto(sock, buffer, size, 0, (struct sockaddr *)
		&udpServAddr, sizeof(udpServAddr)) == size) return size;
	else DieWithError("sendto() sent a different number of bytes than expected");
}


int unicast_net::reciv(char *buffer, unsigned long *IP_Sender, unsigned short size)
{
	int ucleng = sizeof(udpClntAddr);

	if ((sSize = recvfrom(sock, buffer, size, 0,
		(struct sockaddr *) &udpClntAddr, (socklen_t*)&ucleng)) < 0)
		DieWithError("recvfrom() failed ");
	else
	{
		*IP_Sender = udpClntAddr.sin_addr.s_addr;
		return sSize;
	}
}

// end
