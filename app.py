"""
Graphical Password Authentication System
Professional Dissertation Project
Complete Implementation with Google Material Design Icons
Advanced Features, Animations, and Full Responsiveness

FIXED: Dashboard now correctly displays email, created_at, last_login.
"""

from flask import Flask, render_template_string, request, jsonify, session, redirect, url_for
from flask_sqlalchemy import SQLAlchemy
from datetime import datetime, timedelta
from functools import wraps
import json
import os
import csv
import math
import hashlib
import secrets
import numpy as np
from scipy.spatial.distance import euclidean
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
import smtplib
import threading

# ============================================================================
# CONFIGURATION
# ============================================================================

class Config:
    SECRET_KEY = os.environ.get('SECRET_KEY') or secrets.token_hex(32)
    basedir = os.path.abspath(os.path.dirname(__file__))
    SQLALCHEMY_DATABASE_URI = 'sqlite:///' + os.path.join(basedir, 'database', 'users.db')
    SQLALCHEMY_TRACK_MODIFICATIONS = False
    
    # Security settings
    MAX_LOGIN_ATTEMPTS = 5
    LOCKOUT_DURATION_MINUTES = 15
    PATTERN_TOLERANCE = 0.15
    PATTERN_SAMPLES_REQUIRED = 5
    MIN_PATTERN_STRENGTH = 30  # Minimum strength score to accept
    
    # Session settings
    SESSION_TIMEOUT_MINUTES = 30
    
    # Email settings (optional - for notifications)
    EMAIL_ENABLED = False
    SMTP_SERVER = 'smtp.gmail.com'
    SMTP_PORT = 587
    SMTP_USERNAME = 'your-email@gmail.com'
    SMTP_PASSWORD = 'your-app-password'

# ============================================================================
# DATABASE SETUP
# ============================================================================

db = SQLAlchemy()

class User(db.Model):
    __tablename__ = 'users'
    
    id = db.Column(db.Integer, primary_key=True)
    email = db.Column(db.String(120), unique=True, nullable=False, index=True)
    pattern_samples = db.Column(db.Text)
    pattern_type = db.Column(db.String(50), default='free_draw')
    pattern_strength = db.Column(db.Float)
    pattern_created_at = db.Column(db.DateTime, default=datetime.utcnow)
    pattern_updated_at = db.Column(db.DateTime)
    pattern_history = db.Column(db.Text)  # JSON list of old patterns
    
    # Authentication metrics
    total_login_attempts = db.Column(db.Integer, default=0)
    successful_logins = db.Column(db.Integer, default=0)
    failed_attempts = db.Column(db.Integer, default=0)
    locked_until = db.Column(db.DateTime)
    
    # Session management
    session_token = db.Column(db.String(256))
    last_activity = db.Column(db.DateTime)
    
    # Timestamps
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    last_login = db.Column(db.DateTime)
    last_failed_login = db.Column(db.DateTime)
    
    def set_pattern_samples(self, patterns_list):
        self.pattern_samples = json.dumps(patterns_list)
    
    def get_pattern_samples(self):
        return json.loads(self.pattern_samples) if self.pattern_samples else []
    
    def is_locked(self):
        if self.locked_until and self.locked_until > datetime.utcnow():
            return True
        return False
    
    def get_remaining_lockout_time(self):
        if self.locked_until and self.locked_until > datetime.utcnow():
            return (self.locked_until - datetime.utcnow()).seconds
        return 0
    
    def increment_failed_attempts(self):
        self.failed_attempts += 1
        self.total_login_attempts += 1
        self.last_failed_login = datetime.utcnow()
        
        if self.failed_attempts >= 5:
            self.locked_until = datetime.utcnow() + timedelta(minutes=15)
    
    def reset_failed_attempts(self):
        self.failed_attempts = 0
        self.locked_until = None
        self.successful_logins += 1
        self.total_login_attempts += 1
        self.last_login = datetime.utcnow()
    
    def update_pattern_history(self, new_pattern):
        history = json.loads(self.pattern_history) if self.pattern_history else []
        history.append({
            'timestamp': datetime.utcnow().isoformat(),
            'pattern': new_pattern
        })
        # Keep only last 5 patterns
        self.pattern_history = json.dumps(history[-5:])

# ============================================================================
# PATTERN MATCHING & ANALYSIS
# ============================================================================

class PatternAnalyzer:
    """Advanced pattern analysis for strength and quality"""
    
    @staticmethod
    def calculate_strength(pattern):
        """Calculate pattern strength score (0-100)"""
        points = pattern.get('points', [])
        if not points:
            return 0
        
        score = 0
        
        # 1. Pattern length (more points = stronger)
        point_count = len(points)
        score += min(point_count / 200 * 30, 30)
        
        # 2. Stroke count variety
        stroke_count = pattern.get('strokeCount', 0)
        score += min(stroke_count / 5 * 20, 20)
        
        # 3. Spatial coverage
        xs = [p['x'] for p in points]
        ys = [p['y'] for p in points]
        
        if xs and ys:
            width = max(xs) - min(xs)
            height = max(ys) - min(ys)
            canvas_area = pattern.get('canvasWidth', 400) * pattern.get('canvasHeight', 400)
            coverage = (width * height) / canvas_area
            score += min(coverage * 25, 25)
        
        # 4. Direction variety
        if len(points) > 1:
            directions = []
            for i in range(1, len(points)):
                dx = points[i]['x'] - points[i-1]['x']
                dy = points[i]['y'] - points[i-1]['y']
                if dx != 0 or dy != 0:
                    angle = math.degrees(math.atan2(dy, dx))
                    directions.append(angle)
            
            if directions:
                # Count unique direction quadrants
                quadrants = set()
                for angle in directions:
                    if -45 <= angle < 45: quadrants.add('right')
                    elif 45 <= angle < 135: quadrants.add('down')
                    elif angle >= 135 or angle < -135: quadrants.add('left')
                    else: quadrants.add('up')
                
                score += len(quadrants) / 4 * 15
        
        # 5. Complexity (intersections)
        if len(points) > 4:
            intersections = PatternAnalyzer.count_intersections(points)
            score += min(intersections / 10 * 10, 10)
        
        return min(score, 100)
    
    @staticmethod
    def count_intersections(points):
        """Count line intersections in pattern"""
        intersections = 0
        segments = []
        
        # Create segments from consecutive points
        for i in range(len(points) - 1):
            segments.append((
                (points[i]['x'], points[i]['y']),
                (points[i+1]['x'], points[i+1]['y'])
            ))
        
        # Check for intersections
        for i in range(len(segments)):
            for j in range(i + 2, len(segments)):
                if PatternAnalyzer.segments_intersect(segments[i], segments[j]):
                    intersections += 1
        
        return intersections
    
    @staticmethod
    def segments_intersect(seg1, seg2):
        """Check if two line segments intersect"""
        (x1, y1), (x2, y2) = seg1
        (x3, y3), (x4, y4) = seg2
        
        def ccw(A, B, C):
            return (C[1]-A[1]) * (B[0]-A[0]) > (B[1]-A[1]) * (C[0]-A[0])
        
        return ccw((x1,y1), (x3,y3), (x4,y4)) != ccw((x2,y2), (x3,y3), (x4,y4)) and \
               ccw((x1,y1), (x2,y2), (x3,y3)) != ccw((x1,y1), (x2,y2), (x4,y4))
    
    @staticmethod
    def get_strength_label(score):
        """Get human-readable strength label"""
        if score >= 80:
            return 'Very Strong', '#00c853'
        elif score >= 60:
            return 'Strong', '#64dd17'
        elif score >= 40:
            return 'Medium', '#ffd600'
        elif score >= 20:
            return 'Weak', '#ff9100'
        else:
            return 'Very Weak', '#ff1744'

class PatternMatcher:
    """Enhanced pattern matching with multiple algorithms"""
    
    def __init__(self, tolerance=0.15):
        self.tolerance = tolerance
    
    def verify_pattern(self, input_pattern, stored_samples):
        """Verify input pattern against stored samples with enhanced matching"""
        if not stored_samples:
            return False, 0
        
        best_similarity = 0
        match_count = 0
        
        similarities = []
        for sample in stored_samples:
            similarity = self.calculate_similarity(input_pattern, sample)
            similarities.append(similarity)
            
            if similarity >= (1 - self.tolerance):
                match_count += 1
                best_similarity = max(best_similarity, similarity)
        
        # Calculate overall confidence
        avg_similarity = np.mean(similarities) if similarities else 0
        
        # Require match with at least 2 out of 5 samples
        is_match = match_count >= 2
        
        return is_match, avg_similarity
    
    def calculate_similarity(self, pattern1, pattern2):
        """Enhanced similarity calculation with multiple features"""
        features1 = self.extract_features(pattern1)
        features2 = self.extract_features(pattern2)
        
        if not features1['normalized_points'] or not features2['normalized_points']:
            return 0.0
        
        scores = []
        weights = []
        
        # 1. Stroke count similarity (15%)
        stroke_sim = self.compare_stroke_count(
            features1['stroke_count'], features2['stroke_count']
        )
        scores.append(stroke_sim)
        weights.append(0.15)
        
        # 2. Path similarity using DTW (35%)
        path_sim = self.compare_paths_dtw(
            features1['normalized_points'], features2['normalized_points']
        )
        scores.append(path_sim)
        weights.append(0.35)
        
        # 3. Direction pattern similarity (20%)
        direction_sim = self.compare_direction_patterns(
            features1['direction_sequence'], features2['direction_sequence']
        )
        scores.append(direction_sim)
        weights.append(0.20)
        
        # 4. Shape similarity (15%)
        shape_sim = self.compare_shapes(
            features1['shape_descriptors'], features2['shape_descriptors']
        )
        scores.append(shape_sim)
        weights.append(0.15)
        
        # 5. Velocity profile similarity (15%)
        velocity_sim = self.compare_velocity_profiles(
            features1['velocities'], features2['velocities']
        )
        scores.append(velocity_sim)
        weights.append(0.15)
        
        # Weighted average
        final_score = sum(s * w for s, w in zip(scores, weights))
        
        return final_score
    
    def extract_features(self, pattern):
        """Extract comprehensive features from pattern"""
        points = pattern.get('points', [])
        
        if not points:
            return self.empty_features()
        
        canvas_w = pattern.get('canvasWidth', 400)
        canvas_h = pattern.get('canvasHeight', 400)
        
        # Normalize points
        normalized_points = [
            (p['x'] / canvas_w, p['y'] / canvas_h) 
            for p in points
        ]
        
        # Calculate velocities
        velocities = []
        for i in range(1, len(points)):
            dx = points[i]['x'] - points[i-1]['x']
            dy = points[i]['y'] - points[i-1]['y']
            velocity = math.sqrt(dx**2 + dy**2)
            velocities.append(velocity)
        
        # Direction sequence
        direction_sequence = []
        for i in range(1, len(normalized_points)):
            dx = normalized_points[i][0] - normalized_points[i-1][0]
            dy = normalized_points[i][1] - normalized_points[i-1][1]
            if dx != 0 or dy != 0:
                angle = math.degrees(math.atan2(dy, dx))
                direction_sequence.append(angle)
        
        # Shape descriptors
        xs = [p[0] for p in normalized_points]
        ys = [p[1] for p in normalized_points]
        
        shape_descriptors = {
            'centroid': (np.mean(xs), np.mean(ys)) if xs else (0, 0),
            'width': max(xs) - min(xs) if xs else 0,
            'height': max(ys) - min(ys) if ys else 0,
            'aspect_ratio': (max(xs) - min(xs)) / (max(ys) - min(ys)) if (max(ys) - min(ys)) > 0 else 1,
            'area': (max(xs) - min(xs)) * (max(ys) - min(ys)) if xs and ys else 0
        }
        
        return {
            'stroke_count': pattern.get('strokeCount', 0),
            'normalized_points': normalized_points,
            'direction_sequence': direction_sequence,
            'velocities': velocities,
            'shape_descriptors': shape_descriptors
        }
    
    def empty_features(self):
        return {
            'stroke_count': 0,
            'normalized_points': [],
            'direction_sequence': [],
            'velocities': [],
            'shape_descriptors': {
                'centroid': (0, 0),
                'width': 0,
                'height': 0,
                'aspect_ratio': 1,
                'area': 0
            }
        }
    
    def compare_stroke_count(self, count1, count2):
        if count1 == count2:
            return 1.0
        elif abs(count1 - count2) == 1:
            return 0.7
        else:
            return max(0, 1 - abs(count1 - count2) / max(count1, count2))
    
    def compare_paths_dtw(self, points1, points2):
        """Dynamic Time Warping for path comparison"""
        if not points1 or not points2:
            return 0.0
        
        # Resample to same length
        sample_size = 50
        resampled1 = self.resample_path(points1, sample_size)
        resampled2 = self.resample_path(points2, sample_size)
        
        # Compute DTW distance
        n, m = len(resampled1), len(resampled2)
        dtw = np.zeros((n+1, m+1))
        dtw.fill(float('inf'))
        dtw[0, 0] = 0
        
        for i in range(1, n+1):
            for j in range(1, m+1):
                cost = euclidean(resampled1[i-1], resampled2[j-1])
                dtw[i, j] = cost + min(dtw[i-1, j], dtw[i, j-1], dtw[i-1, j-1])
        
        dtw_distance = dtw[n, m]
        
        # Convert to similarity
        max_possible_distance = math.sqrt(2)  # Diagonal of unit square
        similarity = max(0, 1 - (dtw_distance / (sample_size * max_possible_distance)))
        
        return similarity
    
    def resample_path(self, points, num_samples):
        if len(points) < 2:
            return points * num_samples
        
        # Calculate cumulative distances
        distances = [0]
        for i in range(1, len(points)):
            dist = euclidean(points[i-1], points[i])
            distances.append(distances[-1] + dist)
        
        total_length = distances[-1]
        
        if total_length == 0:
            return [points[0]] * num_samples
        
        # Resample uniformly
        resampled = []
        for i in range(num_samples):
            target_dist = (i / (num_samples - 1)) * total_length
            
            for j in range(len(distances) - 1):
                if distances[j] <= target_dist <= distances[j+1]:
                    if distances[j+1] - distances[j] == 0:
                        t = 0
                    else:
                        t = (target_dist - distances[j]) / (distances[j+1] - distances[j])
                    
                    x = points[j][0] + t * (points[j+1][0] - points[j][0])
                    y = points[j][1] + t * (points[j+1][1] - points[j][1])
                    resampled.append((x, y))
                    break
        
        return resampled
    
    def compare_direction_patterns(self, dirs1, dirs2):
        """Compare sequences of direction changes"""
        if not dirs1 or not dirs2:
            return 0.0
        
        # Create direction histograms (8 bins)
        hist1 = self.create_direction_histogram(dirs1)
        hist2 = self.create_direction_histogram(dirs2)
        
        # Chi-square distance
        chi_square = 0
        for h1, h2 in zip(hist1, hist2):
            if h1 + h2 > 0:
                chi_square += ((h1 - h2) ** 2) / (h1 + h2)
        
        # Convert to similarity
        similarity = max(0, 1 - chi_square / 2)
        
        return similarity
    
    def create_direction_histogram(self, directions, bins=8):
        histogram = [0] * bins
        
        for angle in directions:
            angle = angle % 360
            bin_index = int(angle / (360 / bins))
            histogram[bin_index] += 1
        
        total = sum(histogram)
        if total > 0:
            histogram = [h / total for h in histogram]
        
        return histogram
    
    def compare_shapes(self, shape1, shape2):
        """Compare overall shape characteristics"""
        score = 0
        
        # Aspect ratio similarity
        ar1 = shape1.get('aspect_ratio', 1)
        ar2 = shape2.get('aspect_ratio', 1)
        
        if ar1 > 0 and ar2 > 0:
            ar_similarity = 1 - min(abs(ar1 - ar2) / max(ar1, ar2), 1)
            score += ar_similarity * 0.4
        
        # Area similarity
        area1 = shape1.get('area', 0)
        area2 = shape2.get('area', 0)
        
        if area1 > 0 and area2 > 0:
            area_similarity = 1 - min(abs(area1 - area2) / max(area1, area2), 1)
            score += area_similarity * 0.3
        
        # Centroid distance
        c1 = shape1.get('centroid', (0, 0))
        c2 = shape2.get('centroid', (0, 0))
        centroid_distance = euclidean(c1, c2)
        centroid_similarity = max(0, 1 - centroid_distance)
        score += centroid_similarity * 0.3
        
        return score
    
    def compare_velocity_profiles(self, vel1, vel2):
        """Compare drawing speed patterns"""
        if not vel1 or not vel2:
            return 0.5  # Neutral if no velocity data
        
        # Normalize velocities
        def normalize(v):
            if not v:
                return []
            max_v = max(v)
            return [x / max_v for x in v] if max_v > 0 else v
        
        norm_vel1 = normalize(vel1)
        norm_vel2 = normalize(vel2)
        
        # Compare mean and variance
        if norm_vel1 and norm_vel2:
            mean1, std1 = np.mean(norm_vel1), np.std(norm_vel1)
            mean2, std2 = np.mean(norm_vel2), np.std(norm_vel2)
            
            mean_sim = 1 - min(abs(mean1 - mean2), 1)
            std_sim = 1 - min(abs(std1 - std2), 1)
            
            return (mean_sim * 0.5 + std_sim * 0.5)
        
        return 0.5

# ============================================================================
# LOGGING & ANALYTICS
# ============================================================================

class AdvancedLogger:
    """Enhanced logging for research analysis"""
    
    def __init__(self):
        self.log_dir = 'logs'
        os.makedirs(self.log_dir, exist_ok=True)
        
        # Initialize different log files
        self.login_log = os.path.join(self.log_dir, 'login_attempts.csv')
        self.pattern_log = os.path.join(self.log_dir, 'pattern_metrics.csv')
        self.feedback_log = os.path.join(self.log_dir, 'user_feedback.csv')
        self.performance_log = os.path.join(self.log_dir, 'system_performance.csv')
        
        self.initialize_logs()
    
    def initialize_logs(self):
        """Create log files with headers"""
        
        if not os.path.exists(self.login_log):
            with open(self.login_log, 'w', newline='') as f:
                writer = csv.writer(f)
                writer.writerow([
                    'Timestamp', 'Email', 'Success', 'Similarity_Score',
                    'Failed_Attempts', 'Login_Duration_Seconds',
                    'IP_Address', 'User_Agent', 'Pattern_Strength'
                ])
        
        if not os.path.exists(self.pattern_log):
            with open(self.pattern_log, 'w', newline='') as f:
                writer = csv.writer(f)
                writer.writerow([
                    'Timestamp', 'Email', 'Action', 'Pattern_Length',
                    'Stroke_Count', 'Coverage_Area', 'Direction_Variety',
                    'Strength_Score', 'Sample_Number'
                ])
        
        if not os.path.exists(self.feedback_log):
            with open(self.feedback_log, 'w', newline='') as f:
                writer = csv.writer(f)
                writer.writerow([
                    'Timestamp', 'Email', 'Rating', 'Ease_of_Use',
                    'Security_Perception', 'Comments'
                ])
        
        if not os.path.exists(self.performance_log):
            with open(self.performance_log, 'w', newline='') as f:
                writer = csv.writer(f)
                writer.writerow([
                    'Timestamp', 'Endpoint', 'Response_Time_ms',
                    'Status_Code', 'Error_Message'
                ])
    
    def log_login_attempt(self, email, success, similarity, failed_attempts, 
                          duration, pattern_strength, ip='N/A', user_agent='N/A'):
        """Log detailed login attempt"""
        with open(self.login_log, 'a', newline='') as f:
            writer = csv.writer(f)
            writer.writerow([
                datetime.utcnow().isoformat(),
                email,
                'Success' if success else 'Failed',
                f'{similarity:.4f}',
                failed_attempts,
                f'{duration:.2f}',
                ip,
                user_agent,
                f'{pattern_strength:.1f}'
            ])
    
    def log_pattern_metrics(self, email, action, pattern, strength, sample_num=0):
        """Log pattern characteristics"""
        points = pattern.get('points', [])
        
        # Calculate metrics
        pattern_length = len(points)
        stroke_count = pattern.get('strokeCount', 0)
        
        # Coverage
        if points:
            xs = [p['x'] for p in points]
            ys = [p['y'] for p in points]
            canvas_w = pattern.get('canvasWidth', 400)
            canvas_h = pattern.get('canvasHeight', 400)
            coverage = ((max(xs) - min(xs)) * (max(ys) - min(ys))) / (canvas_w * canvas_h)
        else:
            coverage = 0
        
        # Direction variety
        if len(points) > 1:
            directions = set()
            for i in range(1, len(points)):
                dx = points[i]['x'] - points[i-1]['x']
                dy = points[i]['y'] - points[i-1]['y']
                if dx != 0 or dy != 0:
                    angle = math.degrees(math.atan2(dy, dx))
                    directions.add(int(angle / 45))
            direction_variety = len(directions) / 8
        else:
            direction_variety = 0
        
        with open(self.pattern_log, 'a', newline='') as f:
            writer = csv.writer(f)
            writer.writerow([
                datetime.utcnow().isoformat(),
                email,
                action,
                pattern_length,
                stroke_count,
                f'{coverage:.3f}',
                f'{direction_variety:.3f}',
                f'{strength:.1f}',
                sample_num
            ])
    
    def log_feedback(self, email, rating, ease_of_use, security_perception, comments=''):
        """Log user feedback"""
        with open(self.feedback_log, 'a', newline='') as f:
            writer = csv.writer(f)
            writer.writerow([
                datetime.utcnow().isoformat(),
                email,
                rating,
                ease_of_use,
                security_perception,
                comments
            ])
    
    def log_performance(self, endpoint, response_time, status_code, error=''):
        """Log system performance"""
        with open(self.performance_log, 'a', newline='') as f:
            writer = csv.writer(f)
            writer.writerow([
                datetime.utcnow().isoformat(),
                endpoint,
                f'{response_time:.2f}',
                status_code,
                error
            ])

# ============================================================================
# EMAIL NOTIFICATIONS (Optional)
# ============================================================================

class EmailNotifier:
    """Send email notifications for security events"""
    
    def __init__(self, app_config):
        self.enabled = app_config.EMAIL_ENABLED
        self.smtp_server = app_config.SMTP_SERVER
        self.smtp_port = app_config.SMTP_PORT
        self.username = app_config.SMTP_USERNAME
        self.password = app_config.SMTP_PASSWORD
    
    def send_async(self, subject, recipient, body):
        """Send email asynchronously"""
        if not self.enabled:
            return
        
        def send():
            try:
                msg = MIMEMultipart()
                msg['From'] = self.username
                msg['To'] = recipient
                msg['Subject'] = subject
                msg.attach(MIMEText(body, 'html'))
                
                with smtplib.SMTP(self.smtp_server, self.smtp_port) as server:
                    server.starttls()
                    server.login(self.username, self.password)
                    server.send_message(msg)
            except Exception as e:
                print(f"Email error: {e}")
        
        thread = threading.Thread(target=send)
        thread.start()
    
    def send_lockout_notification(self, email):
        """Notify user of account lockout"""
        subject = "🔒 Account Locked - Graphical Password System"
        body = f"""
        <html>
        <body style="font-family: Arial, sans-serif;">
            <h2>Account Security Alert</h2>
            <p>Your account ({email}) has been <strong>temporarily locked</strong> 
               due to multiple failed login attempts.</p>
            <p><strong>Lockout Duration:</strong> 15 minutes</p>
            <p>If this wasn't you, please contact support immediately.</p>
            <hr>
            <p style="color: #666; font-size: 12px;">
                Graphical Password Authentication System
            </p>
        </body>
        </html>
        """
        self.send_async(subject, email, body)
    
    def send_suspicious_activity(self, email):
        """Notify user of suspicious activity"""
        subject = "⚠️ Suspicious Activity Detected"
        body = f"""
        <html>
        <body style="font-family: Arial, sans-serif;">
            <h2>Suspicious Activity Alert</h2>
            <p>We detected unusual login activity on your account ({email}).</p>
            <p>Your account has been secured, but please review your recent activity.</p>
            <hr>
            <p style="color: #666; font-size: 12px;">
                Graphical Password Authentication System
            </p>
        </body>
        </html>
        """
        self.send_async(subject, email, body)

# ============================================================================
# FLASK APPLICATION
# ============================================================================

app = Flask(__name__)
app.config.from_object(Config)
db.init_app(app)

# Initialize components
logger = AdvancedLogger()
email_notifier = EmailNotifier(Config)

os.makedirs('database', exist_ok=True)
os.makedirs('logs', exist_ok=True)

with app.app_context():
    db.create_all()

# ============================================================================
# DECORATORS
# ============================================================================

def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'user_id' not in session:
            return redirect(url_for('login_page'))
        
        # Check session timeout
        last_activity = session.get('last_activity')
        if last_activity:
            last_activity = datetime.fromisoformat(last_activity)
            if (datetime.utcnow() - last_activity).seconds > Config.SESSION_TIMEOUT_MINUTES * 60:
                session.clear()
                return redirect(url_for('login_page'))
        
        session['last_activity'] = datetime.utcnow().isoformat()
        return f(*args, **kwargs)
    return decorated_function

def performance_monitor(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        start_time = datetime.utcnow()
        try:
            result = f(*args, **kwargs)
            response_time = (datetime.utcnow() - start_time).total_seconds() * 1000
            logger.log_performance(request.endpoint, response_time, 200)
            return result
        except Exception as e:
            response_time = (datetime.utcnow() - start_time).total_seconds() * 1000
            logger.log_performance(request.endpoint, response_time, 500, str(e))
            raise
    return decorated_function

# ============================================================================
# BEAUTIFUL UI WITH GOOGLE MATERIAL ICONS
# ============================================================================

UI_STYLE = """
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700;800;900&display=swap');
@import url('https://fonts.googleapis.com/icon?family=Material+Icons');

:root {
    --primary: #6366f1;
    --primary-dark: #4f46e5;
    --primary-light: #818cf8;
    --secondary: #8b5cf6;
    --accent: #06b6d4;
    --success: #10b981;
    --warning: #f59e0b;
    --danger: #ef4444;
    --info: #3b82f6;
    
    --gray-50: #f9fafb;
    --gray-100: #f3f4f6;
    --gray-200: #e5e7eb;
    --gray-300: #d1d5db;
    --gray-400: #9ca3af;
    --gray-500: #6b7280;
    --gray-600: #4b5563;
    --gray-700: #374151;
    --gray-800: #1f2937;
    --gray-900: #111827;
    
    --gradient-primary: linear-gradient(135deg, #6366f1 0%, #8b5cf6 50%, #a855f7 100%);
    --gradient-success: linear-gradient(135deg, #059669 0%, #10b981 100%);
    --gradient-danger: linear-gradient(135deg, #dc2626 0%, #ef4444 100%);
    --gradient-warning: linear-gradient(135deg, #d97706 0%, #f59e0b 100%);
    
    --shadow-xs: 0 1px 2px rgba(0, 0, 0, 0.05);
    --shadow-sm: 0 1px 3px rgba(0, 0, 0, 0.1), 0 1px 2px rgba(0, 0, 0, 0.06);
    --shadow-md: 0 4px 6px rgba(0, 0, 0, 0.07), 0 2px 4px rgba(0, 0, 0, 0.06);
    --shadow-lg: 0 10px 15px rgba(0, 0, 0, 0.1), 0 4px 6px rgba(0, 0, 0, 0.05);
    --shadow-xl: 0 20px 25px rgba(0, 0, 0, 0.1), 0 10px 10px rgba(0, 0, 0, 0.04);
    --shadow-2xl: 0 25px 50px rgba(0, 0, 0, 0.25);
    
    --radius-xs: 4px;
    --radius-sm: 6px;
    --radius-md: 8px;
    --radius-lg: 12px;
    --radius-xl: 16px;
    --radius-2xl: 24px;
    --radius-full: 9999px;
    
    --transition-fast: 150ms cubic-bezier(0.4, 0, 0.2, 1);
    --transition-base: 300ms cubic-bezier(0.4, 0, 0.2, 1);
    --transition-slow: 500ms cubic-bezier(0.4, 0, 0.2, 1);
}

* {
    margin: 0;
    padding: 0;
    box-sizing: border-box;
}

body {
    font-family: 'Inter', -apple-system, BlinkMacSystemFont, sans-serif;
    background: linear-gradient(135deg, #667eea 0%, #764ba2 25%, #f093fb 50%, #f5576c 75%, #4facfe 100%);
    background-size: 400% 400%;
    animation: gradientBG 15s ease infinite;
    min-height: 100vh;
    display: flex;
    justify-content: center;
    align-items: center;
    padding: 20px;
    position: relative;
    overflow-x: hidden;
}

@keyframes gradientBG {
    0% { background-position: 0% 50%; }
    25% { background-position: 100% 0%; }
    50% { background-position: 100% 100%; }
    75% { background-position: 0% 100%; }
    100% { background-position: 0% 50%; }
}

body::before {
    content: '';
    position: fixed;
    top: 0;
    left: 0;
    right: 0;
    bottom: 0;
    background-image: 
        radial-gradient(circle at 20% 80%, rgba(255,255,255,0.1) 0%, transparent 50%),
        radial-gradient(circle at 80% 20%, rgba(255,255,255,0.15) 0%, transparent 50%),
        radial-gradient(circle at 40% 40%, rgba(255,255,255,0.08) 0%, transparent 50%),
        radial-gradient(circle at 60% 60%, rgba(255,255,255,0.1) 0%, transparent 50%);
    pointer-events: none;
    z-index: 0;
    animation: particleFloat 20s ease-in-out infinite;
}

@keyframes particleFloat {
    0%, 100% { transform: translate(0, 0) scale(1); }
    25% { transform: translate(10px, -10px) scale(1.05); }
    50% { transform: translate(-5px, -15px) scale(0.95); }
    75% { transform: translate(-15px, 5px) scale(1.02); }
}

.container {
    background: rgba(255, 255, 255, 0.98);
    backdrop-filter: blur(30px);
    -webkit-backdrop-filter: blur(30px);
    border-radius: var(--radius-2xl);
    box-shadow: var(--shadow-2xl), 0 0 0 1px rgba(255, 255, 255, 0.1);
    padding: 48px 40px;
    max-width: 560px;
    width: 100%;
    position: relative;
    z-index: 1;
    animation: slideUpFade 0.6s cubic-bezier(0.4, 0, 0.2, 1);
    border: 1px solid rgba(255, 255, 255, 0.2);
}

.container-wide {
    max-width: 700px;
}

@keyframes slideUpFade {
    from {
        opacity: 0;
        transform: translateY(40px) scale(0.95);
    }
    to {
        opacity: 1;
        transform: translateY(0) scale(1);
    }
}

.logo-container {
    text-align: center;
    margin-bottom: 32px;
}

.logo-icon {
    width: 88px;
    height: 88px;
    background: var(--gradient-primary);
    border-radius: var(--radius-xl);
    margin: 0 auto 20px;
    display: flex;
    align-items: center;
    justify-content: center;
    box-shadow: 0 12px 40px rgba(99, 102, 241, 0.4);
    animation: logoFloat 3s ease-in-out infinite;
    position: relative;
    overflow: hidden;
}

.logo-icon::after {
    content: '';
    position: absolute;
    top: -50%;
    left: -50%;
    width: 200%;
    height: 200%;
    background: linear-gradient(45deg, transparent, rgba(255,255,255,0.1), transparent);
    transform: rotate(45deg);
    animation: logoShine 3s ease-in-out infinite;
}

@keyframes logoFloat {
    0%, 100% { transform: translateY(0px) rotate(0deg); }
    25% { transform: translateY(-8px) rotate(1deg); }
    75% { transform: translateY(4px) rotate(-1deg); }
}

@keyframes logoShine {
    0%, 100% { transform: translateX(-100%) rotate(45deg); }
    50% { transform: translateX(100%) rotate(45deg); }
}

.logo-icon .material-icons {
    font-size: 44px;
    color: white;
    position: relative;
    z-index: 1;
}

h1 {
    color: var(--gray-900);
    text-align: center;
    margin-bottom: 8px;
    font-size: 32px;
    font-weight: 800;
    letter-spacing: -0.5px;
    background: var(--gradient-primary);
    -webkit-background-clip: text;
    -webkit-text-fill-color: transparent;
    background-clip: text;
}

.subtitle {
    color: var(--gray-500);
    text-align: center;
    margin-bottom: 36px;
    font-size: 15px;
    font-weight: 400;
    line-height: 1.6;
}

.form-group {
    margin-bottom: 24px;
}

.form-label {
    display: flex;
    align-items: center;
    gap: 8px;
    margin-bottom: 10px;
    color: var(--gray-700);
    font-weight: 600;
    font-size: 14px;
    letter-spacing: 0.3px;
}

.form-label .material-icons {
    font-size: 20px;
    color: var(--primary);
}

.input-wrapper {
    position: relative;
    transition: var(--transition-base);
}

.input-wrapper .material-icons {
    position: absolute;
    left: 16px;
    top: 50%;
    transform: translateY(-50%);
    font-size: 22px;
    color: var(--gray-400);
    z-index: 1;
    transition: var(--transition-base);
}

input[type="email"],
input[type="text"],
input[type="password"] {
    width: 100%;
    padding: 14px 16px 14px 48px;
    border: 2px solid var(--gray-200);
    border-radius: var(--radius-lg);
    font-size: 15px;
    font-family: 'Inter', sans-serif;
    transition: var(--transition-base);
    background: var(--gray-50);
    color: var(--gray-800);
}

input:focus {
    outline: none;
    border-color: var(--primary);
    background: white;
    box-shadow: 0 0 0 4px rgba(99, 102, 241, 0.1);
}

.canvas-section {
    margin-bottom: 24px;
}

.canvas-header {
    display: flex;
    align-items: center;
    justify-content: space-between;
    margin-bottom: 12px;
}

.canvas-title {
    display: flex;
    align-items: center;
    gap: 8px;
    font-weight: 600;
    color: var(--gray-700);
    font-size: 14px;
}

.canvas-title .material-icons {
    font-size: 20px;
    color: var(--primary);
}

.canvas-container {
    background: var(--gray-50);
    border: 2px solid var(--gray-200);
    border-radius: var(--radius-xl);
    padding: 24px;
    margin-bottom: 20px;
    display: flex;
    justify-content: center;
    transition: var(--transition-base);
    position: relative;
    overflow: hidden;
}

.canvas-container::before {
    content: '';
    position: absolute;
    inset: 0;
    background: 
        linear-gradient(45deg, transparent 48%, rgba(99, 102, 241, 0.03) 50%, transparent 52%);
    background-size: 30px 30px;
    pointer-events: none;
}

.canvas-container:hover {
    border-color: var(--primary-light);
    box-shadow: 0 8px 30px rgba(99, 102, 241, 0.12);
    transform: translateY(-2px);
}

.canvas-container.no-feedback {
    background: var(--gray-900);
    border-color: var(--gray-700);
}

.canvas-container.no-feedback::before {
    background: 
        linear-gradient(45deg, transparent 48%, rgba(99, 102, 241, 0.05) 50%, transparent 52%);
    background-size: 30px 30px;
}

canvas {
    cursor: crosshair;
    border-radius: var(--radius-md);
    touch-action: none;
    background: white;
    box-shadow: var(--shadow-md);
    transition: var(--transition-base);
}

.no-feedback canvas {
    background: var(--gray-800);
    box-shadow: 0 0 30px rgba(99, 102, 241, 0.15);
}

.security-badge {
    display: flex;
    align-items: center;
    gap: 10px;
    padding: 14px 18px;
    background: rgba(245, 158, 11, 0.08);
    border: 1px solid rgba(245, 158, 11, 0.2);
    border-radius: var(--radius-lg);
    margin-bottom: 20px;
    color: #92400e;
    font-size: 13px;
    font-weight: 500;
    backdrop-filter: blur(10px);
}

.security-badge .material-icons {
    font-size: 22px;
    color: var(--warning);
}

.btn {
    padding: 14px 28px;
    border: none;
    border-radius: var(--radius-lg);
    font-size: 15px;
    font-weight: 600;
    cursor: pointer;
    transition: var(--transition-base);
    flex: 1;
    position: relative;
    overflow: hidden;
    letter-spacing: 0.3px;
    font-family: 'Inter', sans-serif;
    display: inline-flex;
    align-items: center;
    justify-content: center;
    gap: 8px;
    text-decoration: none;
}

.btn .material-icons {
    font-size: 20px;
}

.btn::before {
    content: '';
    position: absolute;
    top: 50%;
    left: 50%;
    width: 0;
    height: 0;
    border-radius: 50%;
    background: rgba(255, 255, 255, 0.3);
    transform: translate(-50%, -50%);
    transition: width 0.6s, height 0.6s;
}

.btn:active::before {
    width: 400px;
    height: 400px;
}

.btn-primary {
    background: var(--gradient-primary);
    color: white;
    box-shadow: 0 4px 20px rgba(99, 102, 241, 0.4);
}

.btn-primary:hover {
    transform: translateY(-3px);
    box-shadow: 0 8px 30px rgba(99, 102, 241, 0.5);
}

.btn-secondary {
    background: white;
    color: var(--primary);
    border: 2px solid var(--primary);
}

.btn-secondary:hover {
    background: var(--primary);
    color: white;
    transform: translateY(-3px);
    box-shadow: 0 8px 30px rgba(99, 102, 241, 0.3);
}

.btn-success {
    background: var(--gradient-success);
    color: white;
    width: 100%;
    margin-top: 8px;
    box-shadow: 0 4px 20px rgba(16, 185, 129, 0.4);
}

.btn-success:hover {
    transform: translateY(-3px);
    box-shadow: 0 8px 30px rgba(16, 185, 129, 0.5);
}

.btn-danger {
    background: var(--gradient-danger);
    color: white;
    box-shadow: 0 4px 20px rgba(239, 68, 68, 0.4);
}

.btn-danger:hover {
    transform: translateY(-3px);
    box-shadow: 0 8px 30px rgba(239, 68, 68, 0.5);
}

.btn-outline {
    background: transparent;
    color: var(--primary);
    border: 2px solid var(--primary);
}

.btn-outline:hover {
    background: var(--primary);
    color: white;
    transform: translateY(-3px);
    box-shadow: 0 8px 30px rgba(99, 102, 241, 0.3);
}

.btn:disabled {
    opacity: 0.5;
    cursor: not-allowed;
    transform: none !important;
}

.btn-group {
    display: flex;
    gap: 12px;
    margin-bottom: 20px;
}

.progress-section {
    margin: 28px 0;
}

.progress-header {
    display: flex;
    justify-content: space-between;
    align-items: center;
    margin-bottom: 10px;
}

.progress-label {
    font-size: 13px;
    color: var(--gray-600);
    font-weight: 500;
}

.progress-percentage {
    font-size: 13px;
    font-weight: 700;
    color: var(--primary);
}

.progress-bar {
    width: 100%;
    height: 10px;
    background: var(--gray-200);
    border-radius: var(--radius-full);
    overflow: hidden;
    box-shadow: inset 0 2px 4px rgba(0,0,0,0.06);
}

.progress-fill {
    height: 100%;
    background: var(--gradient-primary);
    transition: width 0.6s cubic-bezier(0.4, 0, 0.2, 1);
    width: 0%;
    border-radius: var(--radius-full);
    position: relative;
}

.progress-fill::after {
    content: '';
    position: absolute;
    top: 0;
    left: 0;
    right: 0;
    bottom: 0;
    background: linear-gradient(90deg, 
        transparent 0%, 
        rgba(255,255,255,0.4) 50%, 
        transparent 100%);
    animation: shimmer 2s infinite;
}

@keyframes shimmer {
    0% { transform: translateX(-100%); }
    100% { transform: translateX(200%); }
}

.strength-meter {
    margin-top: 20px;
    padding: 16px;
    background: var(--gray-50);
    border-radius: var(--radius-lg);
    border: 1px solid var(--gray-200);
}

.strength-header {
    display: flex;
    justify-content: space-between;
    align-items: center;
    margin-bottom: 8px;
}

.strength-label {
    font-size: 13px;
    font-weight: 600;
    color: var(--gray-600);
}

.strength-value {
    font-size: 13px;
    font-weight: 700;
}

.strength-bar {
    width: 100%;
    height: 8px;
    background: var(--gray-200);
    border-radius: var(--radius-full);
    overflow: hidden;
}

.strength-fill {
    height: 100%;
    border-radius: var(--radius-full);
    transition: width 0.6s ease, background 0.6s ease;
}

.alert {
    padding: 16px 20px;
    border-radius: var(--radius-lg);
    margin-top: 20px;
    display: none;
    animation: slideDown 0.4s ease;
    font-weight: 500;
    font-size: 14px;
    display: flex;
    align-items: center;
    gap: 10px;
}

.alert .material-icons {
    font-size: 22px;
}

@keyframes slideDown {
    from {
        opacity: 0;
        transform: translateY(-15px);
    }
    to {
        opacity: 1;
        transform: translateY(0);
    }
}

.alert-error {
    background: #fef2f2;
    color: #991b1b;
    border-left: 4px solid #ef4444;
}

.alert-success {
    background: #f0fdf4;
    color: #166534;
    border-left: 4px solid #10b981;
}

.alert-warning {
    background: #fffbeb;
    color: #92400e;
    border-left: 4px solid #f59e0b;
}

.alert-info {
    background: #eff6ff;
    color: #1e40af;
    border-left: 4px solid #3b82f6;
}

.card {
    background: white;
    border-radius: var(--radius-xl);
    padding: 24px;
    margin-bottom: 20px;
    box-shadow: var(--shadow-sm);
    border: 1px solid var(--gray-100);
    transition: var(--transition-base);
}

.card:hover {
    box-shadow: var(--shadow-lg);
    transform: translateY(-2px);
}

.card-header {
    display: flex;
    align-items: center;
    gap: 12px;
    margin-bottom: 20px;
    padding-bottom: 16px;
    border-bottom: 1px solid var(--gray-100);
}

.card-header .material-icons {
    font-size: 28px;
    color: var(--primary);
    background: rgba(99, 102, 241, 0.1);
    padding: 10px;
    border-radius: var(--radius-lg);
}

.card-title {
    font-size: 18px;
    font-weight: 700;
    color: var(--gray-800);
}

.card-subtitle {
    font-size: 13px;
    color: var(--gray-500);
}

.info-grid {
    display: grid;
    gap: 0;
}

.info-item {
    display: flex;
    justify-content: space-between;
    align-items: center;
    padding: 16px 0;
    border-bottom: 1px solid var(--gray-100);
    transition: var(--transition-fast);
}

.info-item:last-child {
    border-bottom: none;
}

.info-item:hover {
    background: var(--gray-50);
    margin: 0 -24px;
    padding: 16px 24px;
}

.info-label {
    display: flex;
    align-items: center;
    gap: 8px;
    font-weight: 600;
    color: var(--gray-600);
    font-size: 13px;
    text-transform: uppercase;
    letter-spacing: 0.5px;
}

.info-label .material-icons {
    font-size: 18px;
    color: var(--primary);
}

.info-value {
    color: var(--gray-800);
    font-weight: 500;
    font-size: 15px;
    text-align: right;
}

.badge {
    display: inline-flex;
    align-items: center;
    gap: 6px;
    padding: 6px 14px;
    border-radius: var(--radius-full);
    font-size: 12px;
    font-weight: 600;
    letter-spacing: 0.3px;
}

.badge-success {
    background: #d1fae5;
    color: #065f46;
}

.badge-warning {
    background: #fef3c7;
    color: #92400e;
}

.badge-danger {
    background: #fee2e2;
    color: #991b1b;
}

.badge-info {
    background: #dbeafe;
    color: #1e40af;
}

.nav-links {
    text-align: center;
    margin-top: 32px;
    padding-top: 24px;
    border-top: 1px solid var(--gray-100);
}

.nav-links a {
    color: var(--primary);
    text-decoration: none;
    font-weight: 500;
    font-size: 14px;
    transition: var(--transition-fast);
    padding: 8px 16px;
    border-radius: var(--radius-full);
    display: inline-flex;
    align-items: center;
    gap: 6px;
}

.nav-links a:hover {
    background: rgba(99, 102, 241, 0.08);
    text-decoration: none;
}

.nav-links a .material-icons {
    font-size: 18px;
}

.features-grid {
    display: grid;
    grid-template-columns: repeat(2, 1fr);
    gap: 16px;
    margin: 32px 0;
}

.feature-card {
    background: var(--gray-50);
    padding: 24px;
    border-radius: var(--radius-xl);
    text-align: center;
    transition: var(--transition-base);
    border: 1px solid var(--gray-200);
    cursor: default;
}

.feature-card:hover {
    transform: translateY(-5px);
    box-shadow: var(--shadow-lg);
    border-color: var(--primary-light);
    background: white;
}

.feature-icon {
    font-size: 36px;
    margin-bottom: 12px;
    display: block;
}

.feature-title {
    font-weight: 700;
    color: var(--gray-800);
    font-size: 14px;
    margin-bottom: 6px;
}

.feature-desc {
    color: var(--gray-500);
    font-size: 12px;
    line-height: 1.5;
}

.timer-display {
    text-align: center;
    padding: 16px;
    background: var(--gray-50);
    border-radius: var(--radius-lg);
    font-size: 24px;
    font-weight: 700;
    color: var(--danger);
    display: none;
}

.timer-display .material-icons {
    font-size: 20px;
    vertical-align: middle;
}

@media (max-width: 768px) {
    .container {
        padding: 32px 24px;
        border-radius: var(--radius-xl);
        max-width: 100%;
    }
    
    h1 {
        font-size: 26px;
    }
    
    .logo-icon {
        width: 72px;
        height: 72px;
    }
    
    .logo-icon .material-icons {
        font-size: 36px;
    }
    
    .btn-group {
        flex-direction: column;
    }
    
    .features-grid {
        grid-template-columns: 1fr;
    }
    
    .info-item:hover {
        margin: 0 -16px;
        padding: 16px;
    }
}

@media (max-width: 480px) {
    .container {
        padding: 24px 16px;
    }
    
    h1 {
        font-size: 22px;
    }
    
    canvas {
        width: 100%;
        height: auto;
    }
}

@keyframes pulse {
    0%, 100% { opacity: 1; }
    50% { opacity: 0.5; }
}

.animate-pulse {
    animation: pulse 2s cubic-bezier(0.4, 0, 0.6, 1) infinite;
}

@keyframes spin {
    from { transform: rotate(0deg); }
    to { transform: rotate(360deg); }
}

.animate-spin {
    animation: spin 1s linear infinite;
}

::-webkit-scrollbar {
    width: 8px;
}

::-webkit-scrollbar-track {
    background: var(--gray-100);
}

::-webkit-scrollbar-thumb {
    background: var(--gray-300);
    border-radius: var(--radius-full);
}

::-webkit-scrollbar-thumb:hover {
    background: var(--gray-400);
}
"""

# ============================================================================
# HTML PAGES WITH GOOGLE ICONS
# ============================================================================

INDEX_PAGE = f"""
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Graphical Password System</title>
    <style>{UI_STYLE}</style>
</head>
<body>
    <div class="container container-wide">
        <div class="logo-container">
            <div class="logo-icon">
                <span class="material-icons">security</span>
            </div>
            <h1>Graphical Password System</h1>
            <p class="subtitle">
                Advanced Pattern-Based Authentication<br>
                Secure • Intuitive • Research-Backed
            </p>
        </div>
        
        <div style="text-align: center; margin: 40px 0;">
            <div class="btn-group" style="justify-content: center;">
                <a href="/register" class="btn btn-primary" style="flex: 0 1 auto; padding: 16px 36px; font-size: 16px;">
                    <span class="material-icons">person_add</span>
                    Create Account
                </a>
                <a href="/login" class="btn btn-outline" style="flex: 0 1 auto; padding: 16px 36px; font-size: 16px;">
                    <span class="material-icons">login</span>
                    Sign In
                </a>
            </div>
        </div>
        
        <div class="features-grid">
            <div class="feature-card">
                <span class="feature-icon material-icons">gesture</span>
                <div class="feature-title">Draw to Authenticate</div>
                <div class="feature-desc">Create your unique pattern as your password</div>
            </div>
            <div class="feature-card">
                <span class="feature-icon material-icons">visibility_off</span>
                <div class="feature-title">No Visual Feedback</div>
                <div class="feature-desc">Pattern invisible during login for security</div>
            </div>
            <div class="feature-card">
                <span class="feature-icon material-icons">lock</span>
                <div class="feature-title">Account Protection</div>
                <div class="feature-desc">Auto-lock after 5 failed attempts</div>
            </div>
            <div class="feature-card">
                <span class="feature-icon material-icons">analytics</span>
                <div class="feature-title">Research Analytics</div>
                <div class="feature-desc">Comprehensive logging for analysis</div>
            </div>
        </div>
        
        <div class="nav-links">
            <p style="color: var(--gray-400); font-size: 12px; display: flex; align-items: center; justify-content: center; gap: 6px;">
                <span class="material-icons" style="font-size: 16px;">school</span>
                Dissertation Project • Graphical Password Authentication
            </p>
        </div>
    </div>
</body>
</html>
"""

REGISTER_PAGE = f"""
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Register - Graphical Password System</title>
    <style>{UI_STYLE}</style>
</head>
<body>
    <div class="container">
        <div class="logo-container">
            <div class="logo-icon">
                <span class="material-icons">person_add</span>
            </div>
            <h1>Create Account</h1>
            <p class="subtitle">Draw your unique pattern password</p>
        </div>
        
        <div class="form-group">
            <label class="form-label">
                <span class="material-icons">email</span>
                Email Address
            </label>
            <div class="input-wrapper">
                <span class="material-icons">alternate_email</span>
                <input type="email" id="email" name="email" required 
                       placeholder="you@example.com" autocomplete="email">
            </div>
        </div>
        
        <div class="canvas-section">
            <div class="canvas-header">
                <div class="canvas-title">
                    <span class="material-icons">draw</span>
                    Draw Your Pattern
                </div>
                <span class="badge badge-info">Registration Mode</span>
            </div>
            
            <p style="color: var(--gray-500); font-size: 13px; margin-bottom: 16px;">
                Draw the <strong>same pattern 5 times</strong> for better accuracy
            </p>
            
            <div class="canvas-container" id="canvasWrapper">
                <canvas id="patternCanvas"></canvas>
            </div>
            
            <div class="btn-group">
                <button id="savePattern" class="btn btn-primary">
                    <span class="material-icons">save</span>
                    Save Sample <span id="sampleCount">1</span>/5
                </button>
                <button id="clearCanvas" class="btn btn-secondary">
                    <span class="material-icons">refresh</span>
                    Clear
                </button>
            </div>
            
            <div class="progress-section">
                <div class="progress-header">
                    <span class="progress-label">Progress</span>
                    <span class="progress-percentage" id="progressPercent">0%</span>
                </div>
                <div class="progress-bar">
                    <div class="progress-fill" id="progressFill"></div>
                </div>
            </div>
            
            <div class="strength-meter" id="strengthMeter" style="display: none;">
                <div class="strength-header">
                    <span class="strength-label">Pattern Strength</span>
                    <span class="strength-value" id="strengthLabel">-</span>
                </div>
                <div class="strength-bar">
                    <div class="strength-fill" id="strengthFill" style="width: 0%;"></div>
                </div>
            </div>
        </div>
        
        <button id="registerBtn" class="btn btn-success" disabled>
            <span class="material-icons">how_to_reg</span>
            Complete Registration
        </button>
        
        <div id="message" class="alert" style="display: none;"></div>
        
        <div class="nav-links">
            <a href="/login">
                <span class="material-icons">login</span>
                Already have an account? Sign In
            </a>
            <br><br>
            <a href="/">
                <span class="material-icons">arrow_back</span>
                Back to Home
            </a>
        </div>
    </div>
    
    <script>
        class PatternCanvas {{
            constructor(canvasId, showFeedback = true) {{
                this.canvas = document.getElementById(canvasId);
                this.ctx = this.canvas.getContext('2d');
                this.showFeedback = showFeedback;
                this.isDrawing = false;
                this.points = [];
                this.strokeCount = 0;
                this.startTime = null;
                
                this.initializeCanvas();
                this.attachEventListeners();
            }}
            
            initializeCanvas() {{
                const size = Math.min(380, window.innerWidth - 80);
                this.canvas.width = size;
                this.canvas.height = size;
                this.drawGrid();
                this.ctx.strokeStyle = '#6366f1';
                this.ctx.lineWidth = 3;
                this.ctx.lineCap = 'round';
                this.ctx.lineJoin = 'round';
            }}
            
            drawGrid() {{
                this.ctx.strokeStyle = '#e5e7eb';
                this.ctx.lineWidth = 1;
                
                const step = this.canvas.width / 8;
                for (let x = 0; x <= this.canvas.width; x += step) {{
                    this.ctx.beginPath();
                    this.ctx.moveTo(x, 0);
                    this.ctx.lineTo(x, this.canvas.height);
                    this.ctx.stroke();
                }}
                
                for (let y = 0; y <= this.canvas.height; y += step) {{
                    this.ctx.beginPath();
                    this.ctx.moveTo(0, y);
                    this.ctx.lineTo(this.canvas.width, y);
                    this.ctx.stroke();
                }}
                
                this.ctx.strokeStyle = '#d1d5db';
                this.ctx.lineWidth = 2;
                this.ctx.strokeRect(0, 0, this.canvas.width, this.canvas.height);
            }}
            
            attachEventListeners() {{
                this.canvas.addEventListener('mousedown', (e) => this.startDrawing(e));
                this.canvas.addEventListener('mousemove', (e) => this.draw(e));
                this.canvas.addEventListener('mouseup', () => this.stopDrawing());
                this.canvas.addEventListener('mouseleave', () => this.stopDrawing());
                
                this.canvas.addEventListener('touchstart', (e) => this.startDrawing(e));
                this.canvas.addEventListener('touchmove', (e) => this.draw(e));
                this.canvas.addEventListener('touchend', () => this.stopDrawing());
            }}
            
            startDrawing(e) {{
                e.preventDefault();
                this.isDrawing = true;
                this.strokeCount++;
                this.startTime = Date.now();
                
                const pos = this.getPosition(e);
                this.points.push({{
                    x: pos.x, y: pos.y,
                    stroke: this.strokeCount,
                    action: 'down',
                    time: Date.now() - this.startTime
                }});
                
                if (this.showFeedback) {{
                    this.ctx.beginPath();
                    this.ctx.moveTo(pos.x, pos.y);
                }}
            }}
            
            draw(e) {{
                if (!this.isDrawing) return;
                e.preventDefault();
                
                const pos = this.getPosition(e);
                this.points.push({{
                    x: pos.x, y: pos.y,
                    stroke: this.strokeCount,
                    action: 'move',
                    time: Date.now() - this.startTime
                }});
                
                if (this.showFeedback) {{
                    this.ctx.lineTo(pos.x, pos.y);
                    this.ctx.stroke();
                }}
            }}
            
            stopDrawing() {{
                if (!this.isDrawing) return;
                this.isDrawing = false;
                
                if (this.points.length > 0) {{
                    const lastPoint = this.points[this.points.length - 1];
                    this.points.push({{
                        x: lastPoint.x, y: lastPoint.y,
                        stroke: this.strokeCount,
                        action: 'up',
                        time: Date.now() - this.startTime
                    }});
                }}
            }}
            
            getPosition(e) {{
                const rect = this.canvas.getBoundingClientRect();
                const clientX = e.touches ? e.touches[0].clientX : e.clientX;
                const clientY = e.touches ? e.touches[0].clientY : e.clientY;
                
                return {{
                    x: Math.round(clientX - rect.left),
                    y: Math.round(clientY - rect.top)
                }};
            }}
            
            getPattern() {{
                return {{
                    points: this.points,
                    strokeCount: this.strokeCount,
                    canvasWidth: this.canvas.width,
                    canvasHeight: this.canvas.height
                }};
            }}
            
            clear() {{
                this.ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);
                this.drawGrid();
                this.points = [];
                this.strokeCount = 0;
                this.startTime = null;
            }}
        }}
        
        const canvas = new PatternCanvas('patternCanvas', true);
        const patterns = [];
        let currentSample = 0;
        
        function showMessage(message, type) {{
            const messageDiv = document.getElementById('message');
            const icons = {{ error: 'error', success: 'check_circle', warning: 'warning', info: 'info' }};
            messageDiv.innerHTML = `<span class="material-icons">${{icons[type]}}</span> ${{message}}`;
            messageDiv.className = `alert alert-${{type}}`;
            messageDiv.style.display = 'flex';
            
            if (type !== 'error') {{
                setTimeout(() => {{ messageDiv.style.display = 'none'; }}, 5000);
            }}
        }}
        
        function updateProgress() {{
            const percentage = (currentSample / 5) * 100;
            document.getElementById('progressFill').style.width = percentage + '%';
            document.getElementById('progressPercent').textContent = percentage + '%';
        }}
        
        function calculateStrength(pattern) {{
            let score = 0;
            const points = pattern.points;
            
            if (points.length > 0) {{
                score += Math.min(points.length / 200 * 30, 30);
                score += Math.min(pattern.strokeCount / 5 * 20, 20);
                
                const xs = points.map(p => p.x);
                const ys = points.map(p => p.y);
                const width = Math.max(...xs) - Math.min(...xs);
                const height = Math.max(...ys) - Math.min(...ys);
                const coverage = (width * height) / (canvas.canvas.width * canvas.canvas.height);
                score += Math.min(coverage * 25, 25);
            }}
            
            return Math.min(score, 100);
        }}
        
        function updateStrengthMeter(strength) {{
            const meter = document.getElementById('strengthMeter');
            const fill = document.getElementById('strengthFill');
            const label = document.getElementById('strengthLabel');
            
            meter.style.display = 'block';
            fill.style.width = strength + '%';
            
            let color, text;
            if (strength >= 80) {{ color = '#10b981'; text = 'Very Strong'; }}
            else if (strength >= 60) {{ color = '#34d399'; text = 'Strong'; }}
            else if (strength >= 40) {{ color = '#fbbf24'; text = 'Medium'; }}
            else if (strength >= 20) {{ color = '#f97316'; text = 'Weak'; }}
            else {{ color = '#ef4444'; text = 'Very Weak'; }}
            
            fill.style.background = color;
            label.textContent = text;
            label.style.color = color;
        }}
        
        document.getElementById('clearCanvas').addEventListener('click', () => {{
            canvas.clear();
        }});
        
        document.getElementById('savePattern').addEventListener('click', () => {{
            const pattern = canvas.getPattern();
            
            if (pattern.points.length === 0) {{
                showMessage('Please draw a pattern first', 'warning');
                return;
            }}
            
            patterns.push(pattern);
            currentSample++;
            
            document.getElementById('sampleCount').textContent = currentSample + 1;
            updateProgress();
            
            const strength = calculateStrength(pattern);
            updateStrengthMeter(strength);
            
            const wrapper = document.getElementById('canvasWrapper');
            wrapper.style.transform = 'scale(1.03)';
            wrapper.style.borderColor = '#6366f1';
            setTimeout(() => {{
                wrapper.style.transform = 'scale(1)';
                wrapper.style.borderColor = '#e5e7eb';
            }}, 200);
            
            canvas.clear();
            
            if (currentSample >= 5) {{
                document.getElementById('savePattern').disabled = true;
                document.getElementById('registerBtn').disabled = false;
                document.getElementById('progressFill').style.background = 
                    'linear-gradient(135deg, #059669 0%, #10b981 100%)';
                showMessage('All 5 samples collected! Ready to register', 'success');
            }}
        }});
        
        document.getElementById('registerBtn').addEventListener('click', async () => {{
            const email = document.getElementById('email').value;
            
            if (!email) {{
                showMessage('Please enter your email address', 'warning');
                return;
            }}
            
            const btn = document.getElementById('registerBtn');
            const originalHTML = btn.innerHTML;
            btn.disabled = true;
            btn.innerHTML = '<span class="material-icons animate-spin">sync</span> Registering...';
            
            try {{
                const response = await fetch('/register', {{
                    method: 'POST',
                    headers: {{ 'Content-Type': 'application/json' }},
                    body: JSON.stringify({{ email: email, patterns: patterns }})
                }});
                
                const data = await response.json();
                
                if (response.ok) {{
                    showMessage('Registration successful! Redirecting...', 'success');
                    btn.innerHTML = '<span class="material-icons">check_circle</span> Success!';
                    btn.style.background = 'linear-gradient(135deg, #059669 0%, #10b981 100%)';
                    
                    setTimeout(() => {{ window.location.href = '/login'; }}, 1500);
                }} else {{
                    showMessage(data.error || 'Registration failed', 'error');
                    btn.disabled = false;
                    btn.innerHTML = originalHTML;
                }}
            }} catch (error) {{
                showMessage('Network error. Please try again', 'error');
                btn.disabled = false;
                btn.innerHTML = originalHTML;
            }}
        }});
    </script>
</body>
</html>
"""

LOGIN_PAGE = f"""
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Login - Graphical Password System</title>
    <style>{UI_STYLE}</style>
</head>
<body>
    <div class="container">
        <div class="logo-container">
            <div class="logo-icon">
                <span class="material-icons">lock</span>
            </div>
            <h1>Welcome Back</h1>
            <p class="subtitle">Draw your pattern to sign in</p>
        </div>
        
        <div class="form-group">
            <label class="form-label">
                <span class="material-icons">email</span>
                Email Address
            </label>
            <div class="input-wrapper">
                <span class="material-icons">alternate_email</span>
                <input type="email" id="email" name="email" required 
                       placeholder="you@example.com" autocomplete="email">
            </div>
        </div>
        
        <div class="canvas-section">
            <div class="canvas-header">
                <div class="canvas-title">
                    <span class="material-icons">gesture</span>
                    Draw Your Pattern
                </div>
                <span class="badge badge-warning">Secure Mode</span>
            </div>
            
            <div class="security-badge">
                <span class="material-icons">visibility_off</span>
                <span>For security, your pattern will <strong>NOT</strong> be visible while drawing</span>
            </div>
            
            <div class="canvas-container no-feedback" id="canvasWrapper">
                <canvas id="patternCanvas"></canvas>
            </div>
            
            <div class="btn-group">
                <button id="loginBtn" class="btn btn-primary">
                    <span class="material-icons">login</span>
                    Sign In
                </button>
                <button id="clearCanvas" class="btn btn-secondary">
                    <span class="material-icons">refresh</span>
                    Clear
                </button>
            </div>
        </div>
        
        <div id="message" class="alert" style="display: none;"></div>
        <div id="attemptsInfo" style="text-align: center; margin-top: 12px;"></div>
        <div class="timer-display" id="timerDisplay">
            <span class="material-icons">timer</span>
            <span id="timerText"></span>
        </div>
        
        <div class="nav-links">
            <a href="/register">
                <span class="material-icons">person_add</span>
                Don't have an account? Create One
            </a>
            <br><br>
            <a href="/">
                <span class="material-icons">arrow_back</span>
                Back to Home
            </a>
        </div>
    </div>
    
    <script>
        class PatternCanvas {{
            constructor(canvasId, showFeedback = true) {{
                this.canvas = document.getElementById(canvasId);
                this.ctx = this.canvas.getContext('2d');
                this.showFeedback = showFeedback;
                this.isDrawing = false;
                this.points = [];
                this.strokeCount = 0;
                this.startTime = null;
                
                this.initializeCanvas();
                this.attachEventListeners();
            }}
            
            initializeCanvas() {{
                const size = Math.min(380, window.innerWidth - 80);
                this.canvas.width = size;
                this.canvas.height = size;
                this.drawGrid();
                this.ctx.strokeStyle = '#6366f1';
                this.ctx.lineWidth = 3;
                this.ctx.lineCap = 'round';
                this.ctx.lineJoin = 'round';
            }}
            
            drawGrid() {{
                this.ctx.fillStyle = '#1f2937';
                this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
                
                this.ctx.strokeStyle = '#374151';
                this.ctx.lineWidth = 1;
                
                const step = this.canvas.width / 8;
                for (let x = 0; x <= this.canvas.width; x += step) {{
                    this.ctx.beginPath();
                    this.ctx.moveTo(x, 0);
                    this.ctx.lineTo(x, this.canvas.height);
                    this.ctx.stroke();
                }}
                
                for (let y = 0; y <= this.canvas.height; y += step) {{
                    this.ctx.beginPath();
                    this.ctx.moveTo(0, y);
                    this.ctx.lineTo(this.canvas.width, y);
                    this.ctx.stroke();
                }}
                
                this.ctx.strokeStyle = '#6366f1';
                this.ctx.lineWidth = 2;
                this.ctx.strokeRect(0, 0, this.canvas.width, this.canvas.height);
                
                this.ctx.fillStyle = '#6366f1';
                this.ctx.beginPath();
                this.ctx.arc(this.canvas.width/2, this.canvas.height/2, 4, 0, Math.PI * 2);
                this.ctx.fill();
            }}
            
            attachEventListeners() {{
                this.canvas.addEventListener('mousedown', (e) => this.startDrawing(e));
                this.canvas.addEventListener('mousemove', (e) => this.draw(e));
                this.canvas.addEventListener('mouseup', () => this.stopDrawing());
                this.canvas.addEventListener('mouseleave', () => this.stopDrawing());
                
                this.canvas.addEventListener('touchstart', (e) => this.startDrawing(e));
                this.canvas.addEventListener('touchmove', (e) => this.draw(e));
                this.canvas.addEventListener('touchend', () => this.stopDrawing());
            }}
            
            startDrawing(e) {{
                e.preventDefault();
                this.isDrawing = true;
                this.strokeCount++;
                this.startTime = Date.now();
                
                const pos = this.getPosition(e);
                this.points.push({{
                    x: pos.x, y: pos.y,
                    stroke: this.strokeCount,
                    action: 'down',
                    time: Date.now() - this.startTime
                }});
            }}
            
            draw(e) {{
                if (!this.isDrawing) return;
                e.preventDefault();
                
                const pos = this.getPosition(e);
                this.points.push({{
                    x: pos.x, y: pos.y,
                    stroke: this.strokeCount,
                    action: 'move',
                    time: Date.now() - this.startTime
                }});
            }}
            
            stopDrawing() {{
                if (!this.isDrawing) return;
                this.isDrawing = false;
                
                if (this.points.length > 0) {{
                    const lastPoint = this.points[this.points.length - 1];
                    this.points.push({{
                        x: lastPoint.x, y: lastPoint.y,
                        stroke: this.strokeCount,
                        action: 'up',
                        time: Date.now() - this.startTime
                    }});
                }}
            }}
            
            getPosition(e) {{
                const rect = this.canvas.getBoundingClientRect();
                const clientX = e.touches ? e.touches[0].clientX : e.clientX;
                const clientY = e.touches ? e.touches[0].clientY : e.clientY;
                
                return {{
                    x: Math.round(clientX - rect.left),
                    y: Math.round(clientY - rect.top)
                }};
            }}
            
            getPattern() {{
                return {{
                    points: this.points,
                    strokeCount: this.strokeCount,
                    canvasWidth: this.canvas.width,
                    canvasHeight: this.canvas.height
                }};
            }}
            
            clear() {{
                this.ctx.fillStyle = '#1f2937';
                this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
                this.drawGrid();
                this.points = [];
                this.strokeCount = 0;
                this.startTime = null;
            }}
        }}
        
        const canvas = new PatternCanvas('patternCanvas', false);
        
        function showMessage(message, type) {{
            const messageDiv = document.getElementById('message');
            const icons = {{ error: 'error', success: 'check_circle', warning: 'warning', info: 'info' }};
            messageDiv.innerHTML = `<span class="material-icons">${{icons[type]}}</span> ${{message}}`;
            messageDiv.className = `alert alert-${{type}}`;
            messageDiv.style.display = 'flex';
            
            if (type !== 'error') {{
                setTimeout(() => {{ messageDiv.style.display = 'none'; }}, 5000);
            }}
        }}
        
        document.getElementById('clearCanvas').addEventListener('click', () => {{
            canvas.clear();
        }});
        
        document.getElementById('loginBtn').addEventListener('click', async () => {{
            const email = document.getElementById('email').value;
            const pattern = canvas.getPattern();
            
            if (!email) {{
                showMessage('Please enter your email address', 'warning');
                return;
            }}
            
            if (pattern.points.length === 0) {{
                showMessage('Please draw your pattern', 'warning');
                return;
            }}
            
            const btn = document.getElementById('loginBtn');
            const originalHTML = btn.innerHTML;
            btn.disabled = true;
            btn.innerHTML = '<span class="material-icons animate-spin">sync</span> Verifying...';
            
            try {{
                const response = await fetch('/login', {{
                    method: 'POST',
                    headers: {{ 'Content-Type': 'application/json' }},
                    body: JSON.stringify({{ email: email, pattern: pattern }})
                }});
                
                const data = await response.json();
                
                if (response.ok) {{
                    showMessage('Login successful! Redirecting...', 'success');
                    btn.innerHTML = '<span class="material-icons">check_circle</span> Success!';
                    
                    setTimeout(() => {{ window.location.href = data.redirect; }}, 1000);
                }} else {{
                    showMessage(data.error || 'Login failed', 'error');
                    btn.disabled = false;
                    btn.innerHTML = originalHTML;
                    canvas.clear();
                    
                    if (data.locked) {{
                        btn.disabled = true;
                        document.getElementById('attemptsInfo').innerHTML = 
                            '<span class="badge badge-danger"><span class="material-icons" style="font-size:16px;">lock</span> Account Locked</span>';
                        
                        const timerDisplay = document.getElementById('timerDisplay');
                        const timerText = document.getElementById('timerText');
                        timerDisplay.style.display = 'block';
                        
                        let timeLeft = 900; // 15 minutes
                        const timer = setInterval(() => {{
                            const minutes = Math.floor(timeLeft / 60);
                            const seconds = timeLeft % 60;
                            timerText.textContent = `${{minutes}}:${{seconds.toString().padStart(2, '0')}}`;
                            timeLeft--;
                            
                            if (timeLeft < 0) {{
                                clearInterval(timer);
                                timerDisplay.style.display = 'none';
                                btn.disabled = false;
                                document.getElementById('attemptsInfo').innerHTML = '';
                            }}
                        }}, 1000);
                    }} else if (data.remaining_attempts) {{
                        document.getElementById('attemptsInfo').innerHTML = 
                            `<span class="badge badge-warning"><span class="material-icons" style="font-size:16px;">warning</span> ${{data.remaining_attempts}} attempts remaining</span>`;
                    }}
                }}
            }} catch (error) {{
                showMessage('Network error. Please try again', 'error');
                btn.disabled = false;
                btn.innerHTML = originalHTML;
            }}
        }});
    </script>
</body>
</html>
"""

# FIXED DASHBOARD_PAGE: Now using double braces to produce literal {email}, {created_at}, {last_login}
DASHBOARD_PAGE = f"""
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Dashboard - Graphical Password System</title>
    <style>{UI_STYLE}</style>
</head>
<body>
    <div class="container container-wide">
        <div class="logo-container">
            <div class="logo-icon" style="background: var(--gradient-success); box-shadow: 0 12px 40px rgba(16, 185, 129, 0.4);">
                <span class="material-icons">verified_user</span>
            </div>
            <h1>Welcome!</h1>
            <p class="subtitle">You've successfully authenticated</p>
        </div>
        
        <div class="card">
            <div class="card-header">
                <span class="material-icons">account_circle</span>
                <div>
                    <div class="card-title">Account Information</div>
                    <div class="card-subtitle">Your profile details</div>
                </div>
            </div>
            <div class="info-grid">
                <div class="info-item">
                    <span class="info-label">
                        <span class="material-icons">email</span>
                        Email
                    </span>
                    <span class="info-value">{{email}}</span>
                </div>
                <div class="info-item">
                    <span class="info-label">
                        <span class="material-icons">calendar_today</span>
                        Member Since
                    </span>
                    <span class="info-value">{{created_at}}</span>
                </div>
                <div class="info-item">
                    <span class="info-label">
                        <span class="material-icons">schedule</span>
                        Last Login
                    </span>
                    <span class="info-value">{{last_login}}</span>
                </div>
                <div class="info-item">
                    <span class="info-label">
                        <span class="material-icons">security</span>
                        Security Status
                    </span>
                    <span class="info-value">
                        <span class="badge badge-success">
                            <span class="material-icons" style="font-size:14px;">shield</span>
                            Secure
                        </span>
                    </span>
                </div>
            </div>
        </div>
        
        <div class="card" style="text-align: center; background: linear-gradient(135deg, #f0fdf4 0%, #dcfce7 100%);">
            <span class="material-icons" style="font-size: 64px; color: #10b981; margin-bottom: 16px;">celebration</span>
            <h3 style="color: #166534; margin-bottom: 8px;">Authentication Successful</h3>
            <p style="color: #15803d; line-height: 1.6;">
                Your graphical password was verified successfully.<br>
                The system recognized your unique drawing pattern.
            </p>
        </div>
        
        <div style="text-align: center; margin-top: 28px;">
            <a href="/logout" class="btn btn-danger" style="text-decoration: none; display: inline-flex;">
                <span class="material-icons">logout</span>
                Sign Out
            </a>
        </div>
        
        <div class="nav-links">
            <p style="color: var(--gray-400); font-size: 12px; display: flex; align-items: center; justify-content: center; gap: 6px;">
                <span class="material-icons" style="font-size: 16px;">lock</span>
                Secured with Graphical Password Authentication
            </p>
        </div>
    </div>
</body>
</html>
"""

FEEDBACK_PAGE = f"""
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Feedback - Graphical Password System</title>
    <style>{UI_STYLE}</style>
</head>
<body>
    <div class="container">
        <div class="logo-container">
            <div class="logo-icon">
                <span class="material-icons">feedback</span>
            </div>
            <h1>Your Feedback</h1>
            <p class="subtitle">Help us improve the system</p>
        </div>
        
        <div class="form-group">
            <label class="form-label">
                <span class="material-icons">star</span>
                Overall Rating
            </label>
            <div style="display: flex; gap: 8px; margin-top: 8px;" id="starRating">
                <span class="material-icons star" data-rating="1" style="font-size: 36px; cursor: pointer; color: #d1d5db; transition: var(--transition-fast);">star</span>
                <span class="material-icons star" data-rating="2" style="font-size: 36px; cursor: pointer; color: #d1d5db; transition: var(--transition-fast);">star</span>
                <span class="material-icons star" data-rating="3" style="font-size: 36px; cursor: pointer; color: #d1d5db; transition: var(--transition-fast);">star</span>
                <span class="material-icons star" data-rating="4" style="font-size: 36px; cursor: pointer; color: #d1d5db; transition: var(--transition-fast);">star</span>
                <span class="material-icons star" data-rating="5" style="font-size: 36px; cursor: pointer; color: #d1d5db; transition: var(--transition-fast);">star</span>
            </div>
        </div>
        
        <div class="form-group">
            <label class="form-label">
                <span class="material-icons">touch_app</span>
                Ease of Use
            </label>
            <div class="input-wrapper">
                <select id="easeOfUse" style="width: 100%; padding: 14px; border: 2px solid #e5e7eb; border-radius: 12px; font-family: 'Inter', sans-serif; font-size: 15px;">
                    <option value="">Select rating...</option>
                    <option value="5">Very Easy</option>
                    <option value="4">Easy</option>
                    <option value="3">Neutral</option>
                    <option value="2">Difficult</option>
                    <option value="1">Very Difficult</option>
                </select>
            </div>
        </div>
        
        <div class="form-group">
            <label class="form-label">
                <span class="material-icons">security</span>
                Security Perception
            </label>
            <div class="input-wrapper">
                <select id="securityPerception" style="width: 100%; padding: 14px; border: 2px solid #e5e7eb; border-radius: 12px; font-family: 'Inter', sans-serif; font-size: 15px;">
                    <option value="">Select rating...</option>
                    <option value="5">Very Secure</option>
                    <option value="4">Secure</option>
                    <option value="3">Neutral</option>
                    <option value="2">Insecure</option>
                    <option value="1">Very Insecure</option>
                </select>
            </div>
        </div>
        
        <div class="form-group">
            <label class="form-label">
                <span class="material-icons">comment</span>
                Comments
            </label>
            <textarea id="comments" rows="3" placeholder="Share your thoughts..." 
                      style="width: 100%; padding: 14px; border: 2px solid #e5e7eb; border-radius: 12px; font-family: 'Inter', sans-serif; font-size: 15px; resize: vertical;"></textarea>
        </div>
        
        <button id="submitFeedback" class="btn btn-primary" style="width: 100%;">
            <span class="material-icons">send</span>
            Submit Feedback
        </button>
        
        <div id="message" class="alert" style="display: none;"></div>
        
        <div class="nav-links">
            <a href="/dashboard">
                <span class="material-icons">arrow_back</span>
                Back to Dashboard
            </a>
        </div>
    </div>
    
    <script>
        let selectedRating = 0;
        
        document.querySelectorAll('.star').forEach(star => {{
            star.addEventListener('mouseover', function() {{
                const rating = this.dataset.rating;
                updateStars(rating);
            }});
            
            star.addEventListener('mouseleave', function() {{
                updateStars(selectedRating);
            }});
            
            star.addEventListener('click', function() {{
                selectedRating = this.dataset.rating;
                updateStars(selectedRating);
            }});
        }});
        
        function updateStars(rating) {{
            document.querySelectorAll('.star').forEach((star, index) => {{
                if (index < rating) {{
                    star.style.color = '#f59e0b';
                }} else {{
                    star.style.color = '#d1d5db';
                }}
            }});
        }}
        
        document.getElementById('submitFeedback').addEventListener('click', async () => {{
            const easeOfUse = document.getElementById('easeOfUse').value;
            const securityPerception = document.getElementById('securityPerception').value;
            const comments = document.getElementById('comments').value;
            
            if (!selectedRating || !easeOfUse || !securityPerception) {{
                const msg = document.getElementById('message');
                msg.innerHTML = '<span class="material-icons">warning</span> Please complete all required fields';
                msg.className = 'alert alert-warning';
                msg.style.display = 'flex';
                return;
            }}
            
            try {{
                const response = await fetch('/feedback', {{
                    method: 'POST',
                    headers: {{ 'Content-Type': 'application/json' }},
                    body: JSON.stringify({{
                        rating: selectedRating,
                        ease_of_use: easeOfUse,
                        security_perception: securityPerception,
                        comments: comments
                    }})
                }});
                
                const data = await response.json();
                const msg = document.getElementById('message');
                
                if (response.ok) {{
                    msg.innerHTML = '<span class="material-icons">check_circle</span> ' + data.message;
                    msg.className = 'alert alert-success';
                }} else {{
                    msg.innerHTML = '<span class="material-icons">error</span> ' + (data.error || 'Error submitting feedback');
                    msg.className = 'alert alert-error';
                }}
                msg.style.display = 'flex';
            }} catch (error) {{
                const msg = document.getElementById('message');
                msg.innerHTML = '<span class="material-icons">error</span> Network error';
                msg.className = 'alert alert-error';
                msg.style.display = 'flex';
            }}
        }});
    </script>
</body>
</html>
"""

# ============================================================================
# ROUTES (FIXED DASHBOARD ROUTE)
# ============================================================================

@app.route('/')
def index():
    return INDEX_PAGE

@app.route('/register', methods=['GET'])
def register_page():
    return REGISTER_PAGE

@app.route('/register', methods=['POST'])
@performance_monitor
def register():
    data = request.get_json()
    email = data.get('email')
    patterns = data.get('patterns')
    
    if not email or not patterns:
        return jsonify({'error': 'Email and patterns are required'}), 400
    
    if len(patterns) != Config.PATTERN_SAMPLES_REQUIRED:
        return jsonify({'error': f'Exactly {Config.PATTERN_SAMPLES_REQUIRED} pattern samples required'}), 400
    
    if User.query.filter_by(email=email).first():
        return jsonify({'error': 'Email already registered'}), 400
    
    # Calculate average pattern strength
    strengths = [PatternAnalyzer.calculate_strength(p) for p in patterns]
    avg_strength = np.mean(strengths)
    
    if avg_strength < Config.MIN_PATTERN_STRENGTH:
        return jsonify({
            'error': f'Pattern too weak (strength: {avg_strength:.0f}/100). Please create a more complex pattern.'
        }), 400
    
    user = User(
        email=email,
        pattern_strength=avg_strength,
        pattern_created_at=datetime.utcnow()
    )
    user.set_pattern_samples(patterns)
    
    db.session.add(user)
    db.session.commit()
    
    # Log pattern metrics
    for i, pattern in enumerate(patterns):
        logger.log_pattern_metrics(email, 'registration', pattern, strengths[i], i+1)
    
    return jsonify({
        'message': 'Registration successful',
        'pattern_strength': f'{avg_strength:.0f}/100'
    }), 201

@app.route('/login', methods=['GET'])
def login_page():
    return LOGIN_PAGE

@app.route('/login', methods=['POST'])
@performance_monitor
def login():
    start_time = datetime.utcnow()
    data = request.get_json()
    email = data.get('email')
    login_pattern = data.get('pattern')
    
    if not email or not login_pattern:
        return jsonify({'error': 'Email and pattern are required'}), 400
    
    user = User.query.filter_by(email=email).first()
    if not user:
        return jsonify({'error': 'Invalid credentials'}), 401
    
    if user.is_locked():
        remaining_time = user.get_remaining_lockout_time()
        minutes = remaining_time // 60
        seconds = remaining_time % 60
        return jsonify({
            'error': f'Account locked. Try again in {minutes}:{seconds:02d}',
            'locked': True
        }), 403
    
    stored_patterns = user.get_pattern_samples()
    matcher = PatternMatcher(tolerance=Config.PATTERN_TOLERANCE)
    
    is_match, similarity = matcher.verify_pattern(login_pattern, stored_patterns)
    
    # Calculate login duration
    login_duration = (datetime.utcnow() - start_time).total_seconds()
    
    # Log attempt
    input_strength = PatternAnalyzer.calculate_strength(login_pattern)
    logger.log_login_attempt(
        email, is_match, similarity, user.failed_attempts,
        login_duration, input_strength,
        request.remote_addr, request.user_agent.string
    )
    
    if is_match:
        user.reset_failed_attempts()
        db.session.commit()
        
        session['user_id'] = user.id
        session['email'] = email
        session['last_activity'] = datetime.utcnow().isoformat()
        
        return jsonify({
            'message': 'Login successful',
            'redirect': '/dashboard',
            'similarity': f'{similarity:.2%}'
        }), 200
    else:
        user.increment_failed_attempts()
        db.session.commit()
        
        remaining_attempts = Config.MAX_LOGIN_ATTEMPTS - user.failed_attempts
        
        if remaining_attempts <= 0:
            email_notifier.send_lockout_notification(email)
            return jsonify({
                'error': 'Account locked for 15 minutes due to too many failed attempts.',
                'locked': True
            }), 403
        
        return jsonify({
            'error': f'Invalid pattern. {remaining_attempts} attempts remaining.',
            'remaining_attempts': remaining_attempts
        }), 401

@app.route('/dashboard')
@login_required
def dashboard():
    user = User.query.get(session['user_id'])
    # Now the template contains literal {email}, {created_at}, {last_login}
    return DASHBOARD_PAGE.replace('{email}', user.email)\
                         .replace('{created_at}', user.created_at.strftime('%B %d, %Y'))\
                         .replace('{last_login}', user.last_login.strftime('%B %d, %Y at %H:%M') if user.last_login else 'First login')

@app.route('/feedback', methods=['GET'])
@login_required
def feedback_page():
    return FEEDBACK_PAGE

@app.route('/feedback', methods=['POST'])
@login_required
def submit_feedback():
    data = request.get_json()
    rating = data.get('rating')
    ease_of_use = data.get('ease_of_use')
    security_perception = data.get('security_perception')
    comments = data.get('comments', '')
    
    if not rating or not ease_of_use or not security_perception:
        return jsonify({'error': 'All fields are required'}), 400
    
    logger.log_feedback(session['email'], rating, ease_of_use, security_perception, comments)
    
    return jsonify({'message': 'Thank you for your feedback!'}), 200

@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for('index'))

# Error handlers
@app.errorhandler(404)
def not_found(e):
    return jsonify({'error': 'Page not found'}), 404

@app.errorhandler(500)
def server_error(e):
    return jsonify({'error': 'Internal server error'}), 500

# ============================================================================
# MAIN
# ============================================================================

if __name__ == '__main__':
    print("""
    ╔══════════════════════════════════════════════════════════════╗
    ║                                                              ║
    ║   🔐  Graphical Password Authentication System             ║
    ║       Dissertation Project - Professional Edition           ║
    ║                                                              ║
    ╚══════════════════════════════════════════════════════════════╝
    
    ✨ Starting server with advanced features...
    🌐 Access at: http://localhost:5000
    
    📋 Features:
      ✓ Google Material Design Icons
      ✓ Professional animations & transitions
      ✓ Pattern strength analysis
      ✓ Advanced pattern matching (DTW + ML features)
      ✓ Comprehensive CSV logging
      ✓ User feedback collection
      ✓ Email notifications (configurable)
      ✓ Session management with timeout
      ✓ Mobile-responsive design
      ✓ Touch support for mobile devices
      ✓ Performance monitoring
      ✓ Security best practices
    
    📊 Research Data:
      - Login attempts logged to: logs/login_attempts.csv
      - Pattern metrics logged to: logs/pattern_metrics.csv
      - User feedback logged to: logs/user_feedback.csv
      - Performance data logged to: logs/system_performance.csv
    
    Press Ctrl+C to stop the server
    ═══════════════════════════════════════════════════════════════
    """)
    
    app.run(debug=True, host='0.0.0.0', port=5000)