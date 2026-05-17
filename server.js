const express  = require('express');
const http     = require('http');
const socketIO = require('socket.io');
const cors     = require('cors');
const fs       = require('fs');
const path     = require('path');

const app    = express();
const server = http.createServer(app);

// ─────────────────────────────────────────────
//  Constants
// ─────────────────────────────────────────────
const MAX_MESSAGE_LENGTH     = 500;
const MAX_USERNAME_LENGTH    = 32;
const MAX_HISTORY            = 50;
const CODE_LENGTH            = 9;

const MAX_VERIFY_ATTEMPTS    = 5;
const VERIFY_WINDOW_MS       = 60 * 1000;

const MSG_RATE_MAX           = 4;
const MSG_RATE_WINDOW_MS     = 3000;

const MAX_VERIFY_ATTEMPTS_IP = 15;
const VERIFY_IP_WINDOW_MS    = 60 * 1000;

const MAX_SESSIONS_PER_CODE  = 3;
const UNVERIFIED_TIMEOUT_MS  = 30 * 1000;

const MAX_CODE_USAGE_ENTRIES = 20;

// ─────────────────────────────────────────────
//  Environment Variables
// ─────────────────────────────────────────────
const ADMIN_SECRET   = process.env.ADMIN_SECRET;
const ALLOWED_ORIGIN = process.env.ALLOWED_ORIGIN || 'https://starblast.io';

// ─────────────────────────────────────────────
//  Socket.IO
// ─────────────────────────────────────────────
const io = socketIO(server, {
    cors: {
        origin:      ALLOWED_ORIGIN,
        methods:     ['GET', 'POST'],
        credentials: true
    }
});

app.use(cors({ origin: ALLOWED_ORIGIN }));
app.use(express.json());

// ─────────────────────────────────────────────
//  Admin Auth Middleware
// ─────────────────────────────────────────────
function requireAdminAuth(req, res, next) {
    if (!ADMIN_SECRET) {
        return res.status(503).json({ error: 'Admin access not configured. Set ADMIN_SECRET env var.' });
    }
    const token = req.headers['x-admin-token'];
    if (!token || token !== ADMIN_SECRET) {
        return res.status(401).json({ error: 'Unauthorized' });
    }
    next();
}

// ─────────────────────────────────────────────
//  Input Validation
// ─────────────────────────────────────────────
function sanitizeString(str, maxLength) {
    if (typeof str !== 'string') return null;
    return str.trim().slice(0, maxLength);
}

function isValidUsername(username) {
    if (!username || typeof username !== 'string') return false;
    const trimmed = username.trim();
    if (trimmed.length < 1 || trimmed.length > MAX_USERNAME_LENGTH) return false;
    return /^[a-zA-Z0-9_\- ]+$/.test(trimmed);
}

function isValidMessage(message) {
    if (!message || typeof message !== 'string') return false;
    const trimmed = message.trim();
    return trimmed.length > 0 && trimmed.length <= MAX_MESSAGE_LENGTH;
}

function isValidHexColor(color) {
    return typeof color === 'string' && /^#[0-9a-fA-F]{6}$/.test(color);
}

function isValidHue(hue) {
    return hue === null || hue === undefined || (typeof hue === 'number' && isFinite(hue) && hue >= 0 && hue <= 360);
}

// ─────────────────────────────────────────────
//  Circular Buffer
// ─────────────────────────────────────────────
class CircularBuffer {
    constructor(size) {
        this.size   = size;
        this.buffer = new Array(size);
        this.head   = 0;
        this.count  = 0;
    }
    push(item) {
        this.buffer[this.head] = item;
        this.head  = (this.head + 1) % this.size;
        this.count = Math.min(this.count + 1, this.size);
    }
    toArray() {
        if (this.count < this.size) {
            return this.buffer.slice(0, this.count).filter(Boolean);
        }
        return [
            ...this.buffer.slice(this.head),
            ...this.buffer.slice(0, this.head)
        ].filter(Boolean);
    }
}

// ─────────────────────────────────────────────
//  Whitelist
// ─────────────────────────────────────────────
const WHITELIST_PATH = path.join(__dirname, 'whitelist.txt');
let whitelist = new Set();
let codeUsage = {};

function loadWhitelist() {
    try {
        if (fs.existsSync(WHITELIST_PATH)) {
            const content = fs.readFileSync(WHITELIST_PATH, 'utf8');
            whitelist.clear();
            content.split('\n').forEach(line => {
                const code = line.split('#')[0].trim().toUpperCase();
                if (code.length === CODE_LENGTH) whitelist.add(code);
            });
            console.log(`Whitelist loaded: ${whitelist.size} codes`);
        } else {
            console.log('whitelist.txt not found, creating empty file');
            fs.writeFileSync(
                WHITELIST_PATH,
                '# Enter codes here (9 characters)\n# Example: A3K9X7M2B # for Player1\n'
            );
        }
    } catch (error) {
        console.error('Error loading whitelist:', error);
    }
}

function trackCodeUsage(code, username) {
    const upper = code.toUpperCase();
    if (!codeUsage[upper]) codeUsage[upper] = [];
    if (!codeUsage[upper].includes(username)) {
        if (codeUsage[upper].length >= MAX_CODE_USAGE_ENTRIES) {
            codeUsage[upper].shift();
        }
        codeUsage[upper].push(username);
        console.log(`Code ${upper} used by "${username}"`);
    }
}

function isValidCode(code) {
    return whitelist.has(code.toUpperCase());
}

function getActiveSessionsForCode(code) {
    return Array.from(clients.values()).filter(c => c.code === code.toUpperCase() && c.verified);
}

// ─────────────────────────────────────────────
//  State
// ─────────────────────────────────────────────
const clients          = new Map();
const messageHistory   = new CircularBuffer(MAX_HISTORY);
const verifyAttempts   = new Map();
const msgAttempts      = new Map();
const ipVerifyAttempts = new Map();

function getClientIP(socket) {
    const forwarded = socket.handshake.headers['x-forwarded-for'];
    if (forwarded) return forwarded.split(',')[0].trim();
    return socket.handshake.address;
}

function checkIPVerifyLimit(ip) {
    const now  = Date.now();
    let bucket = ipVerifyAttempts.get(ip);
    if (!bucket || now > bucket.resetAt) {
        bucket = { count: 0, resetAt: now + VERIFY_IP_WINDOW_MS };
        ipVerifyAttempts.set(ip, bucket);
    }
    bucket.count++;
    return bucket.count <= MAX_VERIFY_ATTEMPTS_IP;
}

setInterval(() => {
    const now = Date.now();
    for (const [ip, bucket] of ipVerifyAttempts.entries()) {
        if (now > bucket.resetAt) ipVerifyAttempts.delete(ip);
    }
}, 5 * 60 * 1000);

function broadcastOnlineCount() {
    const verifiedUsers = Array.from(clients.values()).filter(c => c.verified && c.username);
    io.emit('onlineCountUpdate', {
        count: verifiedUsers.length,
        users: verifiedUsers.map(c => c.username)
    });
    console.log(`Online count: ${verifiedUsers.length}`);
}

// ─────────────────────────────────────────────
//  Init
// ─────────────────────────────────────────────
loadWhitelist();

// ─────────────────────────────────────────────
//  HTTP Routes
// ─────────────────────────────────────────────
app.get('/', (req, res) => {
    res.json({
        status:           'Server running',
        time:             new Date().toISOString(),
        connectedClients: clients.size,
        whitelistedCodes: whitelist.size
    });
});

app.get('/reload-whitelist', requireAdminAuth, (req, res) => {
    loadWhitelist();
    res.json({ success: true, message: 'Whitelist reloaded', totalCodes: whitelist.size });
});

app.get('/admin/code-usage', requireAdminAuth, (req, res) => {
    res.json({
        success:    true,
        timestamp:  new Date().toISOString(),
        codeUsage,
        totalCodes: Object.keys(codeUsage).length,
        totalUsers: Object.values(codeUsage).flat().length
    });
});

// ─────────────────────────────────────────────
//  Socket.IO
// ─────────────────────────────────────────────
io.on('connection', (socket) => {
    console.log('New client connected:', socket.id);

    clients.set(socket.id, {
        id:          socket.id,
        username:    null,
        verified:    false,
        code:        null,
        connectedAt: new Date()
    });

    verifyAttempts.set(socket.id, { count: 0, resetAt: Date.now() + VERIFY_WINDOW_MS });
    msgAttempts.set(socket.id,    { count: 0, resetAt: Date.now() + MSG_RATE_WINDOW_MS });

    socket.emit('verifyRequired', { message: 'Please verify with /verify CODE' });

    const unverifiedTimeout = setTimeout(() => {
        const client = clients.get(socket.id);
        if (client && !client.verified) {
            console.log(`Kicking unverified socket: ${socket.id}`);
            socket.disconnect();
        }
    }, UNVERIFIED_TIMEOUT_MS);

    // ── Verify Code ──────────────────────────
    socket.on('verifyCode', (data) => {
        const ip = getClientIP(socket);
        if (!checkIPVerifyLimit(ip)) {
            socket.emit('verifyFailed', { message: 'Too many attempts from your network. Try again later.' });
            socket.disconnect();
            return;
        }

        const attempts = verifyAttempts.get(socket.id);
        if (attempts) {
            if (Date.now() > attempts.resetAt) {
                attempts.count   = 0;
                attempts.resetAt = Date.now() + VERIFY_WINDOW_MS;
            }
            attempts.count++;
            if (attempts.count > MAX_VERIFY_ATTEMPTS) {
                socket.emit('verifyFailed', { message: 'Too many attempts. Disconnecting.' });
                socket.disconnect();
                return;
            }
        }

        if (!data || typeof data !== 'object') return;

        const code     = sanitizeString(data.code,     CODE_LENGTH);
        const username = sanitizeString(data.username, MAX_USERNAME_LENGTH);

        if (!code || code.length !== CODE_LENGTH) {
            socket.emit('verifyFailed', { message: `Code must be exactly ${CODE_LENGTH} characters.` });
            return;
        }

        if (!isValidUsername(username)) {
            socket.emit('verifyFailed', {
                message: 'Invalid username. Use letters, numbers, _ or - only (max 32 chars).'
            });
            return;
        }

        const client = clients.get(socket.id);
        if (!client) return;

        const usernameTaken = Array.from(clients.values()).some(
            c => c.verified && c.username === username && c.id !== socket.id
        );
        if (usernameTaken) {
            socket.emit('verifyFailed', { message: 'Username already in use. Pick a different name.' });
            return;
        }

        if (isValidCode(code)) {
            const activeSessions = getActiveSessionsForCode(code);
            if (activeSessions.length >= MAX_SESSIONS_PER_CODE) {
                socket.emit('verifyFailed', {
                    message: `This code is already in use by ${MAX_SESSIONS_PER_CODE} sessions.`
                });
                return;
            }

            clearTimeout(unverifiedTimeout);

            client.verified = true;
            client.code     = code.toUpperCase();
            client.username = username;

            trackCodeUsage(code, username);
            console.log(`${username} verified with code ${code.toUpperCase()}`);

            socket.emit('verifySuccess', { message: 'Verification successful! Welcome to the chat.' });

            socket.emit('welcome', {
                history:     messageHistory.toArray(),
                onlineUsers: Array.from(clients.values())
                    .filter(c => c.verified && c.username)
                    .map(c => c.username)
            });

            socket.broadcast.emit('userJoined', {
                username,
                message:   `${username} joined the chat`,
                timestamp: new Date().toISOString()
            });

            broadcastOnlineCount();

        } else {
            console.log(`Invalid code attempt from "${username}": ${code}`);
            socket.emit('verifyFailed', { message: 'Code invalid, please try again.' });
        }
    });

    // ── Chat Message ─────────────────────────
    socket.on('chatMessage', (data) => {
        const client = clients.get(socket.id);
        if (!client || !client.verified || !client.username) {
            socket.emit('verifyRequired', { message: 'You must be verified to send messages.' });
            return;
        }

        const msgBucket = msgAttempts.get(socket.id);
        if (msgBucket) {
            if (Date.now() > msgBucket.resetAt) {
                msgBucket.count   = 0;
                msgBucket.resetAt = Date.now() + MSG_RATE_WINDOW_MS;
            }
            msgBucket.count++;
            if (msgBucket.count > MSG_RATE_MAX) {
                socket.emit('rateLimited', { message: 'You are sending messages too fast.' });
                return;
            }
        }

        if (!data || typeof data !== 'object') return;

        const message   = sanitizeString(data.message, MAX_MESSAGE_LENGTH);
        if (!isValidMessage(message)) return;

        const nameColor = isValidHexColor(data.nameColor) ? data.nameColor : '#ffffff';
        const hue       = isValidHue(data.hue) ? (data.hue ?? null) : null;
        const realUser  = client.username;

        const msgObj = {
            id:        Date.now() + Math.random(),
            username:  client.username,
            message,
            nameColor,
            hue,
            realUser,
            timestamp: new Date().toISOString(),
            type:      'user'
        };

        messageHistory.push(msgObj);
        io.emit('newMessage', msgObj);

        console.log(`Message from ${msgObj.username}`);
    });

    // ── Disconnect ───────────────────────────
    socket.on('disconnect', () => {
        clearTimeout(unverifiedTimeout);
        const client = clients.get(socket.id);
        verifyAttempts.delete(socket.id);
        msgAttempts.delete(socket.id);

        if (client && client.verified && client.username) {
            console.log(`Disconnected: ${client.username} (Code: ${client.code})`);
            socket.broadcast.emit('userLeft', {
                username:  client.username,
                message:   `${client.username} left the chat`,
                timestamp: new Date().toISOString()
            });
            clients.delete(socket.id);
            broadcastOnlineCount();
        } else {
            console.log(`Unverified client disconnected: ${socket.id}`);
            clients.delete(socket.id);
        }
    });
});

// ─────────────────────────────────────────────
//  Start
// ─────────────────────────────────────────────
const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
    console.log(`Server running on port ${PORT}`);
    console.log(`Whitelist: ${whitelist.size} codes loaded`);
    console.log(`CORS origin: ${ALLOWED_ORIGIN}`);
    console.log(`Admin auth: ${ADMIN_SECRET ? 'Configured' : 'ADMIN_SECRET not set'}`);
});
